import LeanDag.RedSnapper.Helpers.Votes
import LeanDag.RedSnapper.Model.Certificates

/-!
# Computable certificates

Generated: the filter form of `AtLeast`, decidable surrogates for the
certificate predicates of `Model/Certificates.lean`, and the iffs that
pin them against the audited definitions for universe members. Nothing
here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

section AtLeast

variable {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- Author sets are monotone. -/
theorem authorsOf_mono {s t : Finset BlockId} (h : s ⊆ t) :
    authorsOf U.block s ⊆ authorsOf U.block t :=
  Finset.image_subset_image h

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- The filter form of a threshold: `k` authors among the `P`-blocks of
`s`. -/
theorem atLeast_iff_filter {k : ℕ} {s : Finset BlockId} {P : BlockId → Prop}
    [DecidablePred P] :
    AtLeast U k s P ↔ k ≤ (authorsOf U.block (s.filter P)).card := by
  constructor
  · rintro ⟨t, hts, hP, hk⟩
    have : t ⊆ s.filter P := fun b hb => Finset.mem_filter.mpr ⟨hts hb, hP b hb⟩
    exact hk.trans (Finset.card_le_card (authorsOf_mono this))
  · intro hk
    exact ⟨s.filter P, Finset.filter_subset _ _, fun b hb => (Finset.mem_filter.mp hb).2, hk⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- A threshold reads only the predicate on the blocks of `s`. -/
theorem atLeast_congr {k : ℕ} {s : Finset BlockId} {P Q : BlockId → Prop}
    (h : ∀ b ∈ s, (P b ↔ Q b)) : AtLeast U k s P ↔ AtLeast U k s Q := by
  constructor
  · rintro ⟨t, hts, hP, hk⟩
    exact ⟨t, hts, fun b hb => (h b (hts hb)).mp (hP b hb), hk⟩
  · rintro ⟨t, hts, hQ, hk⟩
    exact ⟨t, hts, fun b hb => (h b (hts hb)).mpr (hQ b hb), hk⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- The blocks of a round are universe members. -/
theorem mem_ids_of_mem_blocksAt {r : ℕ} {b : BlockId} (h : b ∈ blocksAt U r) : b ∈ U.ids :=
  (Finset.mem_filter.mp h).1

end AtLeast

section Surrogates

variable (U : Universe Validator BlockId Tx Obj)

/-- The computable form of `IsFastCert`. -/
def IsFastCertDec (C : BlockId) (tx : Tx) : Prop :=
  IsFastVoteDec U C tx ∧
    quorum Validator ≤
      (authorsOf U.block ((U.block C).parents.filter fun b => IsFastVoteDec U b tx)).card

instance (C : BlockId) (tx : Tx) : Decidable (IsFastCertDec U C tx) := by
  unfold IsFastCertDec; infer_instance

/-- The computable form of `HasCert`. -/
def HasCertDec (b : BlockId) (tx : Tx) : Prop :=
  ∃ C ∈ historyIn U b, IsFastCertDec U C tx

instance (b : BlockId) (tx : Tx) : Decidable (HasCertDec U b tx) := by
  unfold HasCertDec; infer_instance

/-- The computable form of `CertVisible`. -/
def CertVisibleDec (b : BlockId) (tx : Tx) : Prop :=
  quorum Validator ≤
      (authorsOf U.block ((U.block b).parents.filter fun p => IsFastVoteDec U p tx)).card ∨
    ∃ p ∈ (U.block b).parents, HasCertDec U p tx

instance (b : BlockId) (tx : Tx) : Decidable (CertVisibleDec U b tx) := by
  unfold CertVisibleDec; infer_instance

/-- The computable form of `IsSkipCert`. -/
def IsSkipCertDec (C : BlockId) (o : Obj) : Prop :=
  half Validator ≤
    (authorsOf U.block ((U.block C).parents.filter fun b => IsSkipVoteDec U b o)).card

instance (C : BlockId) (o : Obj) : Decidable (IsSkipCertDec U C o) := by
  unfold IsSkipCertDec; infer_instance

/-- The computable form of `IsUnlockCert`. -/
def IsUnlockCertDec (C : BlockId) (o : Obj) : Prop :=
  half Validator ≤
    (authorsOf U.block ((U.block C).parents.filter fun b => IsBotVoteDec U b o)).card

instance (C : BlockId) (o : Obj) : Decidable (IsUnlockCertDec U C o) := by
  unfold IsUnlockCertDec; infer_instance

/-- The computable form of `FastQuorumAt`. -/
def FastQuorumAtDec (r : ℕ) (tx : Tx) : Prop :=
  quorum Validator ≤
    (authorsOf U.block ((blocksAt U r).filter fun C => IsFastCertDec U C tx)).card

instance (r : ℕ) (tx : Tx) : Decidable (FastQuorumAtDec U r tx) := by
  unfold FastQuorumAtDec; infer_instance

end Surrogates

variable {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq Obj] in
/-- A parent-threshold over `IsFastVote` reads as its computable form at
a universe member. -/
theorem atLeast_parents_fastVote_iff {k : ℕ} {C : BlockId} {tx : Tx} (hC : C ∈ U.ids) :
    AtLeast U k (U.block C).parents (fun b => IsFastVote U b tx) ↔
      k ≤ (authorsOf U.block ((U.block C).parents.filter fun b => IsFastVoteDec U b tx)).card := by
  rw [atLeast_congr fun b hb => isFastVote_iff (U.complete C hC b hb), atLeast_iff_filter]

omit [DecidableEq Obj] in
theorem isFastCert_iff {C : BlockId} {tx : Tx} (hC : C ∈ U.ids) :
    IsFastCert U C tx ↔ IsFastCertDec U C tx := by
  unfold IsFastCert IsFastCertDec
  rw [isFastVote_iff hC, atLeast_parents_fastVote_iff hC]

omit [DecidableEq Obj] in
theorem hasCert_iff {b : BlockId} {tx : Tx} (hb : b ∈ U.ids) :
    HasCert U b tx ↔ HasCertDec U b tx := by
  unfold HasCert HasCertDec
  constructor
  · rintro ⟨C, hC, hcert, hr⟩
    exact ⟨C, (mem_historyIn_iff hb).mpr ⟨hC, hr⟩, (isFastCert_iff hC).mp hcert⟩
  · rintro ⟨C, hC, hcert⟩
    obtain ⟨hCid, hr⟩ := (mem_historyIn_iff hb).mp hC
    exact ⟨C, hCid, (isFastCert_iff hCid).mpr hcert, hr⟩

omit [DecidableEq Obj] in
theorem certVisible_iff {b : BlockId} {tx : Tx} (hb : b ∈ U.ids) :
    CertVisible U b tx ↔ CertVisibleDec U b tx := by
  unfold CertVisible CertVisibleDec
  rw [atLeast_parents_fastVote_iff hb]
  constructor
  · rintro (h | ⟨p, hp, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, (hasCert_iff (U.complete b hb p hp)).mp hc⟩
  · rintro (h | ⟨p, hp, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, (hasCert_iff (U.complete b hb p hp)).mpr hc⟩

theorem isSkipCert_iff {C : BlockId} {o : Obj} (hC : C ∈ U.ids) :
    IsSkipCert U C o ↔ IsSkipCertDec U C o := by
  unfold IsSkipCert IsSkipCertDec
  rw [atLeast_congr fun b hb => isSkipVote_iff (U.complete C hC b hb), atLeast_iff_filter]

theorem isUnlockCert_iff {C : BlockId} {o : Obj} (hC : C ∈ U.ids) :
    IsUnlockCert U C o ↔ IsUnlockCertDec U C o := by
  unfold IsUnlockCert IsUnlockCertDec
  rw [atLeast_congr fun b hb => isBotVote_iff (U.complete C hC b hb), atLeast_iff_filter]

omit [DecidableEq Obj] in
theorem fastQuorumAt_iff {r : ℕ} {tx : Tx} :
    FastQuorumAt U r tx ↔ FastQuorumAtDec U r tx := by
  unfold FastQuorumAt FastQuorumAtDec
  rw [atLeast_congr fun C hC => isFastCert_iff (mem_ids_of_mem_blocksAt hC), atLeast_iff_filter]

end RedSnapper

end LeanDag
