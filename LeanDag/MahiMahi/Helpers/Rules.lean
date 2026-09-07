import LeanDag.MahiMahi.Model.Rules
/-!
# Helpers — the rule layer

Generated lemma infrastructure for `Model/Rules.lean`; not part of the
audit surface. Membership unfoldings, the two facts canonical support
supplies (a block votes for at most one candidate per author and round;
a vote excludes a blame), the round arithmetic of a wave, and the three
counting lemmas every safety result rests on: a skipped slot has no
certificate, two certificates name one candidate, and certificates
persist upward through the DAG.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## Unfoldings -/

theorem mem_candidatesAt {q b : BlockId} {a : Validator} {r : ℕ} :
    b ∈ candidatesAt U q a r ↔
      b ∈ U.ids ∧ (U.block b).round = r ∧ (U.block b).creator = a ∧ b ∈ history U q := by
  simp only [candidatesAt, Finset.mem_filter, mem_blocksAt]
  tauto

theorem mem_blamers {w : ℕ} {a : Validator} {r : ℕ} {v : Validator} :
    v ∈ blamers U w a r ↔
      ∃ q ∈ U.ids, (U.block q).round = votingRound w r ∧ Blames U q a r ∧
        (U.block q).creator = v := by
  simp only [blamers, mem_creatorsOf, Finset.mem_filter, mem_blocksAt]
  tauto

/-! ## What canonical support supplies -/

theorem Votes.mem_ids {q L : BlockId} (h : Votes U q L) : L ∈ U.ids :=
  (mem_candidatesAt.mp h.1).1

theorem Votes.mem_history {q L : BlockId} (h : Votes U q L) : L ∈ history U q :=
  (mem_candidatesAt.mp h.1).2.2.2

/-- A block votes for at most one candidate of a given author and round:
both are least in the same candidate set. -/
theorem eq_of_votes {q L₁ L₂ : BlockId} (h₁ : Votes U q L₁) (h₂ : Votes U q L₂)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  have m₁ : L₁ ∈ candidatesAt U q (U.block L₂).creator (U.block L₂).round := by
    rw [← hc, ← hr]; exact h₁.1
  have m₂ : L₂ ∈ candidatesAt U q (U.block L₁).creator (U.block L₁).round := by
    rw [hc, hr]; exact h₂.1
  exact le_antisymm (not_lt.mp (h₁.2 L₂ m₂)) (not_lt.mp (h₂.2 L₁ m₁))

/-- A vote for `L` is not a blame of `L`'s slot. -/
theorem not_blames_of_votes {q L : BlockId} (h : Votes U q L) :
    ¬ Blames U q (U.block L).creator (U.block L).round := by
  intro hb
  have hm := h.1
  rw [Blames] at hb
  rw [hb] at hm
  simp at hm

/-! ## The rounds of a wave -/

theorem decisionRoundAt_eq_votingRound_succ {w r : ℕ} (hw : 2 ≤ w) :
    decisionRoundAt w r = votingRound w r + 1 := by
  unfold decisionRoundAt votingRound
  omega

/-- A vote counted by a decision-round certificate is a voting-round
block of the universe. -/
theorem votesIn_spec {C L q : BlockId} {w r : ℕ} (hw : 2 ≤ w)
    (hC : C ∈ U.ids) (hCr : (U.block C).round = decisionRoundAt w r)
    (hq : q ∈ votesIn U C L) :
    q ∈ U.ids ∧ (U.block q).round = votingRound w r := by
  rw [mem_carriedVotes] at hq
  refine ⟨U.complete C hC q hq.1, ?_⟩
  have := U.round_of_mem_refs hC hq.1
  rw [decisionRoundAt_eq_votingRound_succ hw] at hCr
  omega

/-! ## The three counting lemmas -/

/-- **Skip excludes certificates.** A quorum of blamers and a quorum of
voters at the voting round share a block, which would both vote for `L`
and blame its slot. -/
theorem certificates_eq_empty_of_directSkip {w : ℕ} {a : Validator} {r : ℕ} {L : BlockId}
    (hw : 2 ≤ w) (h : DirectSkip U w a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    certificates U w L r = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  obtain ⟨hCids, hCr, hcert⟩ := mem_certificatesAt.mp hC
  obtain ⟨q, hqv, hqb⟩ := U.exists_common_mem_of_quorums (n := votingRound w r)
    (s := votesIn U C L)
    (t := (blocksAt U (votingRound w r)).filter (fun q => Blames U q a r))
    (fun q hq => votesIn_spec hw hCids hCr hq)
    (fun q hq => mem_blocksAt.mp (Finset.mem_filter.mp hq).1)
    hcert h
  have hv := (mem_carriedVotes.mp hqv).2
  have hb := (Finset.mem_filter.mp hqb).2
  rw [← hLc, ← hLr] at hb
  exact not_blames_of_votes hv hb

/-- **Certificate uniqueness.** Two voter quorums at the voting round
share a block, which votes for one candidate of a given author and
round. -/
theorem eq_of_certificates_nonempty {w r : ℕ} {L₁ L₂ : BlockId} (hw : 2 ≤ w)
    (h₁ : (certificates U w L₁ r).Nonempty) (h₂ : (certificates U w L₂ r).Nonempty)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  obtain ⟨hC₁ids, hC₁r, hcert₁⟩ := mem_certificatesAt.mp hC₁
  obtain ⟨hC₂ids, hC₂r, hcert₂⟩ := mem_certificatesAt.mp hC₂
  obtain ⟨q, hq₁, hq₂⟩ := U.exists_common_mem_of_quorums (n := votingRound w r)
    (fun q hq => votesIn_spec hw hC₁ids hC₁r hq)
    (fun q hq => votesIn_spec hw hC₂ids hC₂r hq) hcert₁ hcert₂
  exact eq_of_votes (mem_carriedVotes.mp hq₁).2 (mem_carriedVotes.mp hq₂).2 hc hr

/-- A direct commit needs a quorum of certificate authors, so at least
one certificate. -/
theorem certificates_nonempty_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ}
    (h : DirectCommit U w L r) : (certificates U w L r).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro hempty
  rw [DirectCommit, hempty] at h
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at h
  have := F.card_validators
  omega

/-- **Certificates persist upward** (the paper's Lemma C.1). A block above
the decision round references a certificate's correct author at the
layer below, and higher blocks reach one through their references. -/
theorem exists_certificate_reaches_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ}
    (h : DirectCommit U w L r) {c : BlockId} (hc : c ∈ U.ids)
    (hcr : decisionRoundAt w r + 1 ≤ (U.block c).round) :
    ∃ C ∈ certificates U w L r, Reaches U c C := by
  have hbase : ∀ c' ∈ U.ids, (U.block c').round = decisionRoundAt w r + 1 →
      ∃ C, C ∈ certificates U w L r ∧ Reaches U c' C := by
    intro c' hc' hc'r
    set T := creatorsOf U.block (certificates U w L r) ∩ (Correct : Finset Validator)
      with hT_def
    have hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = decisionRoundAt w r ∧
        q ∈ certificates U w L r ∧ (U.block q).creator = v := by
      intro v hv
      rw [hT_def, Finset.mem_inter, mem_creatorsOf] at hv
      obtain ⟨⟨q, hq_cert, hq_creator⟩, _⟩ := hv
      obtain ⟨hq_ids, hq_round, -⟩ := mem_certificatesAt.mp hq_cert
      exact ⟨q, hq_ids, hq_round, hq_cert, hq_creator⟩
    have hTc : ∀ v ∈ T, v ∈ (Correct : Finset Validator) :=
      fun _ hv => Finset.mem_of_mem_inter_right hv
    have hcard : F.f + 1 ≤ T.card := card_inter_correct_of_quorum h
    obtain ⟨C, hC_mem, hC_cert⟩ :=
      exists_mem_refs_of_honest_support_of_card
        (Q := fun q => q ∈ certificates U w L r) hT hTc (lt_card_add_quorumCard hcard) hc' hc'r
    exact ⟨C, hC_cert, Reaches.single hC_mem⟩
  exact reaches_pred_of_round_le hbase hc hcr

/-! ## Wave three is the core's rule -/

/-- At the round below a block, a vote is a direct reference: the cone at
that round is the reference set, and distinct creators make the least
candidate the only one. -/
theorem votes_iff_mem_refs {q L : BlockId} (hq : q ∈ U.ids)
    (hr : (U.block L).round + 1 = (U.block q).round) :
    Votes U q L ↔ L ∈ (U.block q).refs := by
  constructor
  · intro h
    exact mem_refs_of_mem_history_of_round_succ hq h.mem_history hr
  · intro hL
    have hLids : L ∈ U.ids := U.complete q hq L hL
    refine ⟨mem_candidatesAt.mpr ⟨hLids, rfl, rfl, mem_history_of_mem_refs hq hL⟩, ?_⟩
    intro L' hL' hlt
    obtain ⟨hL'ids, hL'r, hL'c, hL'h⟩ := mem_candidatesAt.mp hL'
    have hL'refs : L' ∈ (U.block q).refs :=
      mem_refs_of_mem_history_of_round_succ hq hL'h (by omega)
    have := (U.valid q hq).distinct_creators L' hL'refs L hL hL'c
    subst this
    exact lt_irrefl _ hlt

/-- The votes a round-`(r+2)` block counts for a round-`r` block are the
core's. -/
theorem votesIn_eq_of_three {C L : BlockId} {r : ℕ} (hC : C ∈ U.ids)
    (hCr : (U.block C).round = r + 2) (hLr : (U.block L).round = r) :
    votesIn U C L = LeanDag.votesIn U C L := by
  unfold votesIn LeanDag.votesIn
  apply Finset.filter_congr
  intro q hq
  have hqids := U.complete C hC q hq
  have hqr := U.round_of_mem_refs hC hq
  exact votes_iff_mem_refs hqids (by omega)

theorem decisionRoundAt_three (r : ℕ) : decisionRoundAt 3 r = r + 2 := by
  unfold decisionRoundAt
  omega

theorem votingRound_three (r : ℕ) : votingRound 3 r = r + 1 := by
  unfold votingRound
  omega

/-- At wave three the certificates of a round-`r` block are the core's. -/
theorem certificates_eq_of_three {L : BlockId} {r : ℕ} (hLr : (U.block L).round = r) :
    certificates U 3 L r = LeanDag.certificates U L r := by
  unfold certificates LeanDag.certificates certificatesAt
  rw [decisionRoundAt_three]
  apply Finset.filter_congr
  intro C hC
  obtain ⟨hCids, hCr⟩ := mem_blocksAt.mp hC
  unfold CarriesVotes
  rw [show carriedVotes U (Votes U) C L = carriedVotes U (IsVote U) C L from
    votesIn_eq_of_three hCids hCr hLr]

/-- A blame of the slot is a blame of each of its candidates. -/
theorem not_mem_refs_of_blames {q L : BlockId} {a : Validator} {r : ℕ} (hq : q ∈ U.ids)
    (hb : Blames U q a r) (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    L ∉ (U.block q).refs := by
  intro hL
  have : L ∈ candidatesAt U q a r :=
    mem_candidatesAt.mpr ⟨U.complete q hq L hL, hLr, hLc, mem_history_of_mem_refs hq hL⟩
  rw [Blames] at hb
  rw [hb] at this
  simp at this

/-- At wave three, a block at the voting round that does not reference the
only candidate of a slot blames the slot. -/
theorem blames_of_not_mem_refs_of_unique {q L : BlockId} {a : Validator} {r : ℕ}
    (hq : q ∈ U.ids) (hqr : (U.block q).round = r + 1)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r)
    (huniq : ∀ L' ∈ U.ids, (U.block L').creator = a → (U.block L').round = r → L' = L)
    (hL : L ∉ (U.block q).refs) : Blames U q a r := by
  rw [Blames, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  obtain ⟨hbids, hbr, hbc, hbh⟩ := mem_candidatesAt.mp hb
  have := huniq b hbids hbc hbr
  subst this
  exact hL (mem_refs_of_mem_history_of_round_succ hq hbh (by omega))

end MahiMahi

end LeanDag
