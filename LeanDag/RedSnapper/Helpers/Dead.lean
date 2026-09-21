import LeanDag.RedSnapper.Helpers.Certificates
import LeanDag.RedSnapper.Helpers.Anchors
import LeanDag.RedSnapper.Model.Verdict

/-!
# Computable death and release

Generated: `Bool`-valued surrogates for the release recursion of
`Model/Dead.lean` — Bool, so that the recursion can pass the
already-released map to the next level with no decidability
side-conditions — each pinned against the audited definition by an iff
for universe members; the equivalence of the accumulated and per-anchor
readings of release; and the computable forms of the two in-view quorums
of `Model/Verdict.lean`. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [Fintype Tx]
  [F : Faults Validator] [T : Transactions Tx Obj]

section Surrogates

variable (U : Universe Validator BlockId Tx Obj) (A : Anchors U)

/-- The computable form of `DeadGiven`, with the released map as a
`Bool` predicate. -/
def deadGivenB (a : BlockId) (R : Obj → Bool) (tx : Tx) : Bool :=
  decide (∃ tx' : Tx, Conflict tx tx' ∧ HasCertDec U a tx') ||
    decide (∃ C ∈ historyIn U a, IsSkipCertDec U C (T.input tx)) ||
    R (T.input tx)

/-- The computable form of `ResolveReadyGiven`. -/
def resolveReadyGivenB (a : BlockId) (R : Obj → Bool) (o : Obj) : Bool :=
  decide (1 < (candidates U a o).card) &&
    decide (∀ tx ∈ candidates U a o, HasCertDec U a tx → deadGivenB U a R tx = true) &&
    decide (∃ C ∈ historyIn U a, IsSkipCertDec U C o ∨ IsUnlockCertDec U C o)

/-- The computable form of `ReleasedBelow`. -/
def releasedBelowB : ℕ → Obj → Bool
  | 0, _ => false
  | i + 1, o =>
      releasedBelowB i o ||
        match A.seq[i]? with
        | some a => resolveReadyGivenB U a (releasedBelowB i) o
        | none => false

/-- The computable form of `ResolveReadyAt`. -/
def resolveReadyAtB (i : ℕ) (o : Obj) : Bool :=
  match A.seq[i]? with
  | some a => resolveReadyGivenB U a (releasedBelowB U A i) o
  | none => false

/-- The computable form of `ResolvesAt`. -/
def resolvesAtB (i : ℕ) (o : Obj) : Bool :=
  resolveReadyAtB U A i o && decide (∀ j < i, resolveReadyAtB U A j o = false)

/-- The computable form of `DeadAt`. -/
def deadAtB (i : ℕ) (tx : Tx) : Bool :=
  match A.seq[i]? with
  | some a => deadGivenB U a (releasedBelowB U A i) tx
  | none => false

end Surrogates

variable {U : Universe Validator BlockId Tx Obj} {A : Anchors U}

theorem deadGiven_iff {a : BlockId} {tx : Tx} {R : Obj → Prop} {Rb : Obj → Bool}
    (ha : a ∈ U.ids) (hR : ∀ o, R o ↔ Rb o = true) :
    DeadGiven U a R tx ↔ deadGivenB U a Rb tx = true := by
  unfold DeadGiven deadGivenB
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨tx', hc, hcert⟩ | ⟨C, hC, hskip, hr⟩ | h)
    · exact Or.inl (Or.inl ⟨tx', hc, (hasCert_iff ha).mp hcert⟩)
    · exact Or.inl (Or.inr ⟨C, (mem_historyIn_iff ha).mpr ⟨hC, hr⟩,
        (isSkipCert_iff hC).mp hskip⟩)
    · exact Or.inr ((hR _).mp h)
  · rintro ((⟨tx', hc, hcert⟩ | ⟨C, hC, hskip⟩) | h)
    · exact Or.inl ⟨tx', hc, (hasCert_iff ha).mpr hcert⟩
    · obtain ⟨hCid, hr⟩ := (mem_historyIn_iff ha).mp hC
      exact Or.inr (Or.inl ⟨C, hCid, (isSkipCert_iff hCid).mpr hskip, hr⟩)
    · exact Or.inr (Or.inr ((hR _).mpr h))

theorem resolveReadyGiven_iff {a : BlockId} {o : Obj} {R : Obj → Prop} {Rb : Obj → Bool}
    (ha : a ∈ U.ids) (hR : ∀ o, R o ↔ Rb o = true) :
    ResolveReadyGiven U a R o ↔ resolveReadyGivenB U a Rb o = true := by
  unfold ResolveReadyGiven resolveReadyGivenB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hconf, hdead, C, hC, hcert, hr⟩
    refine ⟨⟨(conflicted_iff ha).mp hconf, ?_⟩, ?_⟩
    · intro tx htx hcert'
      exact (deadGiven_iff ha hR).mp
        (hdead tx ((mem_candidates_iff ha).mp htx) ((hasCert_iff ha).mpr hcert'))
    · refine ⟨C, (mem_historyIn_iff ha).mpr ⟨hC, hr⟩, ?_⟩
      rcases hcert with h | h
      · exact Or.inl ((isSkipCert_iff hC).mp h)
      · exact Or.inr ((isUnlockCert_iff hC).mp h)
  · rintro ⟨⟨hconf, hdead⟩, C, hC, hcert⟩
    obtain ⟨hCid, hr⟩ := (mem_historyIn_iff ha).mp hC
    refine ⟨(conflicted_iff ha).mpr hconf, ?_, C, hCid, ?_, hr⟩
    · intro tx htx hcert'
      exact (deadGiven_iff ha hR).mpr
        (hdead tx ((mem_candidates_iff ha).mpr htx) ((hasCert_iff ha).mp hcert'))
    · rcases hcert with h | h
      · exact Or.inl ((isSkipCert_iff hCid).mpr h)
      · exact Or.inr ((isUnlockCert_iff hCid).mpr h)

theorem releasedBelow_iff : ∀ (i : ℕ) (o : Obj),
    ReleasedBelow U A i o ↔ releasedBelowB U A i o = true := by
  intro i
  induction i with
  | zero => intro o; simp [ReleasedBelow, releasedBelowB]
  | succ i ih =>
      intro o
      unfold ReleasedBelow releasedBelowB
      rw [Bool.or_eq_true, ← ih o]
      constructor
      · rintro (h | ⟨a, hi, hready⟩)
        · exact Or.inl h
        · refine Or.inr ?_
          rw [hi]
          exact (resolveReadyGiven_iff (anchor_mem_ids hi) ih).mp hready
      · rintro (h | h)
        · exact Or.inl h
        · rcases hi : A.seq[i]? with - | a
          · rw [hi] at h; simp at h
          · rw [hi] at h
            exact Or.inr ⟨a, rfl, (resolveReadyGiven_iff (anchor_mem_ids hi) ih).mpr h⟩

theorem resolveReadyAt_iff {i : ℕ} {o : Obj} :
    ResolveReadyAt U A i o ↔ resolveReadyAtB U A i o = true := by
  unfold ResolveReadyAt resolveReadyAtB
  cases hi : A.seq[i]? with
  | none =>
      exact ⟨fun ⟨a, ha, _⟩ => by simp at ha, fun h => by simp at h⟩
  | some a =>
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨a', rfl, hready⟩
        exact (resolveReadyGiven_iff (anchor_mem_ids hi) (releasedBelow_iff i)).mp hready
      · intro h
        exact ⟨a, rfl, (resolveReadyGiven_iff (anchor_mem_ids hi) (releasedBelow_iff i)).mpr h⟩

theorem resolvesAt_iff {i : ℕ} {o : Obj} :
    ResolvesAt U A i o ↔ resolvesAtB U A i o = true := by
  unfold ResolvesAt resolvesAtB
  rw [Bool.and_eq_true, decide_eq_true_eq, resolveReadyAt_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by
      rw [← Bool.not_eq_true]
      exact fun hb => h2 j hj (resolveReadyAt_iff.mpr hb)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj hr => by
      have := h2 j hj
      rw [resolveReadyAt_iff] at hr
      simp [hr] at this⟩

theorem deadAt_iff {i : ℕ} {tx : Tx} :
    DeadAt U A i tx ↔ deadAtB U A i tx = true := by
  unfold DeadAt deadAtB
  cases hi : A.seq[i]? with
  | none =>
      exact ⟨fun ⟨a, ha, _⟩ => by simp at ha, fun h => by simp at h⟩
  | some a =>
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨a', rfl, hdead⟩
        exact (deadGiven_iff (anchor_mem_ids hi) (releasedBelow_iff i)).mp hdead
      · intro h
        exact ⟨a, rfl, (deadGiven_iff (anchor_mem_ids hi) (releasedBelow_iff i)).mpr h⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [Fintype Tx] in
/-- The accumulated and per-anchor readings of release agree. -/
theorem releasedBelow_iff_exists {i : ℕ} {o : Obj} :
    ReleasedBelow U A i o ↔ ∃ j < i, ResolveReadyAt U A j o := by
  induction i with
  | zero => simp [ReleasedBelow]
  | succ i ih =>
      unfold ReleasedBelow
      rw [ih]
      constructor
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨i, by omega, h⟩
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_or_ge j i with hlt | hge
        · exact Or.inl ⟨j, hlt, h⟩
        · have : j = i := by omega
          subst this
          exact Or.inr h

section InView

omit [DecidableEq Obj] [Fintype Tx] in
theorem fastQuorumAtInView_iff {V : View U} {r : ℕ} {tx : Tx} :
    FastQuorumAtInView U V r tx ↔
      quorum Validator ≤
        (authorsOf U.block
          (((blocksAt U r) ∩ V.ids).filter fun C => IsFastCertDec U C tx)).card := by
  unfold FastQuorumAtInView
  rw [atLeast_congr fun C hC =>
    isFastCert_iff (mem_ids_of_mem_blocksAt (Finset.mem_inter.mp hC).1), atLeast_iff_filter]

omit [Fintype Tx] in
theorem skipQuorumAtInView_iff {V : View U} {r : ℕ} {o : Obj} :
    SkipQuorumAtInView U V r o ↔
      quorum Validator ≤
        (authorsOf U.block
          (((blocksAt U r) ∩ V.ids).filter fun C => IsSkipCertDec U C o)).card := by
  unfold SkipQuorumAtInView
  rw [atLeast_congr fun C hC =>
    isSkipCert_iff (mem_ids_of_mem_blocksAt (Finset.mem_inter.mp hC).1), atLeast_iff_filter]

end InView

end RedSnapper

end LeanDag
