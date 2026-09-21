import LeanDag.RedSnapper.Model.Five.Moves
import LeanDag.RedSnapper.Helpers.Certificates

/-!
# Computable 5f+1 certificates

Generated: decidable surrogates for the certificate shapes and the move
rule of `Model/Five/`, each pinned against the audited definition by an
iff for universe members, so that witness models decide the computable
side and bridge. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

/-- Stances over a finite transaction type form a `Fintype`, for the
move rule's stance quantifiers. -/
instance [Fintype Tx] : Fintype (Stance Tx) where
  elems := insert Stance.bot (Finset.univ.image Stance.ack)
  complete := by
    intro s
    cases s <;> simp

section Surrogates

variable (U : Universe Validator BlockId Tx Obj)

/-- The computable form of `IsAntiVote`: a unique latest declarer whose
declaration is not `s`. -/
def IsAntiVoteDec (b : BlockId) (o : Obj) (s : Stance Tx) : Prop :=
  ∃ b' ∈ latestDeclarers U (U.block b).author o b, (U.block b').declares o ≠ some s ∧
    ∀ b'' ∈ latestDeclarers U (U.block b).author o b, b'' = b'

instance (b : BlockId) (o : Obj) (s : Stance Tx) : Decidable (IsAntiVoteDec U b o s) := by
  unfold IsAntiVoteDec; infer_instance

/-- The computable form of `IsFullCert`. -/
def IsFullCertDec (C : BlockId) (tx : Tx) : Prop :=
  quorum Validator ≤
    (authorsOf U.block ((U.block C).parents.filter fun b => IsFastVoteDec U b tx)).card

/-- The computable form of `IsHalfCert`. -/
def IsHalfCertDec (C : BlockId) (tx : Tx) : Prop :=
  half Validator ≤
    (authorsOf U.block ((U.block C).parents.filter fun b => IsFastVoteDec U b tx)).card

/-- The computable form of `IsRefutation`. -/
def IsRefutationDec (C : BlockId) (o : Obj) (s : Stance Tx) : Prop :=
  half Validator ≤
    (authorsOf U.block ((U.block C).parents.filter fun b => IsAntiVoteDec U b o s)).card

/-- The computable form of `IsFullUnlockCert`. -/
def IsFullUnlockCertDec (C : BlockId) (o : Obj) : Prop :=
  quorum Validator ≤
    (authorsOf U.block ((U.block C).parents.filter fun b =>
      StanceSomeDec U (U.block b).author o b Stance.bot)).card

/-- The computable form of `MoveDiscipline`. -/
def MoveDisciplineDec : Prop :=
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ (o : Obj) (s s' : Stance Tx),
      StanceSomeDec U (U.block b).author o p s →
      (U.block b).declares o = some s' → s' ≠ s →
      IsRefutationDec U b o s

instance (C : BlockId) (tx : Tx) : Decidable (IsFullCertDec U C tx) := by
  unfold IsFullCertDec; infer_instance

instance (C : BlockId) (tx : Tx) : Decidable (IsHalfCertDec U C tx) := by
  unfold IsHalfCertDec; infer_instance

instance (C : BlockId) (o : Obj) (s : Stance Tx) : Decidable (IsRefutationDec U C o s) := by
  unfold IsRefutationDec; infer_instance

instance (C : BlockId) (o : Obj) : Decidable (IsFullUnlockCertDec U C o) := by
  unfold IsFullUnlockCertDec; infer_instance

instance [Fintype Tx] [Fintype Obj] : Decidable (MoveDisciplineDec U) := by
  unfold MoveDisciplineDec; infer_instance

end Surrogates

variable {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem isAntiVote_iff {b : BlockId} {o : Obj} {s : Stance Tx} (hb : b ∈ U.ids) :
    IsAntiVote U b o s ↔ IsAntiVoteDec U b o s := by
  constructor
  · rintro ⟨s', hst, hne⟩
    obtain ⟨b', hb', hd, hu⟩ := (stanceIs_some_iff hb).mp hst
    exact ⟨b', hb', by simp [hd, hne], hu⟩
  · rintro ⟨b', hb', hd, hu⟩
    have hL := (mem_latestDeclarers_iff hb).mp hb'
    obtain ⟨s'', hs''⟩ : ∃ s'', (U.block b').declares o = some s'' := by
      cases h : (U.block b').declares o with
      | none => exact absurd h hL.1.2.2.2
      | some s'' => exact ⟨s'', rfl⟩
    refine ⟨s'', (stanceIs_some_iff hb).mpr ⟨b', hb', hs'', hu⟩, fun h => hd (h ▸ hs'')⟩

omit [DecidableEq Obj] T in
/-- A parent-threshold over `IsAntiVote` reads as its computable form at
a universe member. -/
theorem atLeast_parents_antiVote_iff {k : ℕ} {C : BlockId} {o : Obj} {s : Stance Tx}
    (hC : C ∈ U.ids) :
    AtLeast U k (U.block C).parents (fun b => IsAntiVote U b o s) ↔
      k ≤ (authorsOf U.block ((U.block C).parents.filter fun b =>
        IsAntiVoteDec U b o s)).card := by
  rw [atLeast_congr fun b hb => isAntiVote_iff (U.complete C hC b hb), atLeast_iff_filter]

omit [DecidableEq Obj] in
theorem isFullCert_iff {C : BlockId} {tx : Tx} (hC : C ∈ U.ids) :
    IsFullCert U C tx ↔ IsFullCertDec U C tx := by
  unfold IsFullCert IsFullCertDec
  rw [atLeast_parents_fastVote_iff hC]

omit [DecidableEq Obj] in
theorem isHalfCert_iff {C : BlockId} {tx : Tx} (hC : C ∈ U.ids) :
    IsHalfCert U C tx ↔ IsHalfCertDec U C tx := by
  unfold IsHalfCert IsHalfCertDec
  rw [atLeast_parents_fastVote_iff hC]

omit [DecidableEq Obj] T in
theorem isRefutation_iff {C : BlockId} {o : Obj} {s : Stance Tx} (hC : C ∈ U.ids) :
    IsRefutation U C o s ↔ IsRefutationDec U C o s := by
  unfold IsRefutation IsRefutationDec
  rw [atLeast_parents_antiVote_iff hC]

omit [DecidableEq Obj] T in
theorem isFullUnlockCert_iff {C : BlockId} {o : Obj} (hC : C ∈ U.ids) :
    IsFullUnlockCert U C o ↔ IsFullUnlockCertDec U C o := by
  unfold IsFullUnlockCert IsFullUnlockCertDec
  rw [atLeast_congr fun b hb => stanceSomeDec_iff (U.complete C hC b hb), atLeast_iff_filter]

omit [DecidableEq Obj] T in
theorem moveDiscipline_iff : MoveDiscipline U ↔ MoveDisciplineDec U := by
  constructor
  · intro h b hb hc p hp hap o s s' hst hd hne
    exact (isRefutation_iff hb).mp (h.move_on_refutation b hb hc p hp hap o s s'
      ((stanceIs_some_iff (U.complete b hb p hp)).mpr hst) hd hne)
  · intro h
    refine ⟨fun b hb hc p hp hap o s s' hst hd hne => ?_⟩
    exact (isRefutation_iff hb).mpr (h b hb hc p hp hap o s s'
      ((stanceIs_some_iff (U.complete b hb p hp)).mp hst) hd hne)

end RedSnapper

end LeanDag
