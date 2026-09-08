import LeanDag.BlackMarlin.Model.Repair
import LeanDag.BlackMarlin.Helpers.Descent
import LeanDag.BlackMarlin.Helpers.Liveness
/-!
# Black Marlin — the repair layer

Generated proof layer; not part of the audit surface. At most one
candidate of a step is supported, the repaired descent takes it where
there is one, and two support-preferring records cannot part at a round
that has one. The repair changes which block a step returns and never
whether it returns one, nor at which round.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {B L : BlockId} {ρ : ℕ}

theorem mem_suppCandidates {A : BlockId} :
    A ∈ suppCandidates U B ↔
      A ∈ maxAnchor U (strongOf U B) ∧ Supported U A (U.block A).round :=
  Finset.mem_filter

/-- **At most one candidate is supported.** The candidates of a step
share a round, and an anchor round has one supported anchor (BM1) — so
where the filter bites there is nothing left to break ties over. -/
theorem suppCandidates_subsingleton :
    ∀ A ∈ suppCandidates U B, ∀ C ∈ suppCandidates U B, A = C := by
  intro A hA C hC
  obtain ⟨hAmax, hAs⟩ := mem_suppCandidates.mp hA
  obtain ⟨hCmax, hCs⟩ := mem_suppCandidates.mp hC
  have hAr := (mem_maxAnchor.mp hAmax).2
  have hCr := (mem_maxAnchor.mp hCmax).2
  have hcr : (U.block A).creator = (U.block C).creator := by
    have hAa := (mem_anchorsOf.mp (mem_maxAnchor.mp hAmax).1).2
    have hCa := (mem_anchorsOf.mp (mem_maxAnchor.mp hCmax).1).2
    unfold IsAnchorBlock at hAa hCa
    rw [hAa, hCa, hAr, hCr]
  exact eq_of_supported hAs (by rw [hCr, ← hAr] at hCs; exact hCs) hcr

/-- **The repaired choice is supported where one is.** -/
theorem descendSupp_supported (h : descendSupp U B = some L)
    (hne : (suppCandidates U B).Nonempty) : Supported U L (U.block L).round := by
  rw [descendSupp, if_pos hne] at h
  exact (mem_suppCandidates.mp (pick_mem h)).2

/-- The repaired choice is still a candidate of the step, so everything
`descend` guarantees of its result holds of this one. -/
theorem descendSupp_mem (h : descendSupp U B = some L) :
    L ∈ maxAnchor U (strongOf U B) := by
  rw [descendSupp] at h
  split at h
  · exact (mem_suppCandidates.mp (pick_mem h)).1
  · exact descend_mem h

theorem descendSupp_mem_ids (hB : B ∈ U.ids) (h : descendSupp U B = some L) : L ∈ U.ids :=
  history_subset_ids hB (mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp
    (descendSupp_mem h)).1).1).2

theorem descendSupp_round_lt (hB : B ∈ U.ids) (h : descendSupp U B = some L) :
    (U.block L).round < (U.block B).round := by
  obtain ⟨hne, hhist⟩ :=
    mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp (descendSupp_mem h)).1).1
  rcases Nat.lt_or_ge (U.block L).round (U.block B).round with hlt | hge
  · exact hlt
  · exact absurd (eq_of_mem_history_of_round_eq hB hhist
      (le_antisymm (round_le_of_mem_history hB hhist) hge)) hne

/-! ## What the repair costs

Nothing structural. The step still returns a block exactly when the
unrepaired one does, and always at the same round, so the rounds a record
flushes at are unchanged and the descent still exhausts. Only *which*
block a step returns can differ. -/

/-- **The repair never stalls the descent.** -/
theorem descendSupp_isSome_iff :
    (descendSupp U B).isSome ↔ (descend U B).isSome := by
  rw [descendSupp]
  split
  · rename_i hne
    constructor
    · intro _
      exact descend_isSome ⟨hne.choose,
        (mem_maxAnchor.mp (mem_suppCandidates.mp hne.choose_spec).1).1⟩
    · intro _; exact pick_isSome hne
  · exact Iff.rfl

/-- **And never moves a step to another round.** -/
theorem descendSupp_round_eq {L' : BlockId} (h : descendSupp U B = some L)
    (h' : descend U B = some L') : (U.block L).round = (U.block L').round := by
  rw [(mem_maxAnchor.mp (descendSupp_mem h)).2, (mem_maxAnchor.mp (descend_mem h')).2]

/-- **Where no candidate is supported, the repair is the original
rule.** So it refines L21–L24 rather than replacing it. -/
theorem descendSupp_eq_descend (h : ¬ (suppCandidates U B).Nonempty) :
    descendSupp U B = descend U B := by
  rw [descendSupp, if_neg h]

/-! ## What the repair yields -/

/-- **Two support-preferring records cannot part at a supported round.**
The whole content of the repair: BM1 makes the supported anchor of a
round unique, and the side-condition puts both records on it. -/
theorem eq_of_supportPreferring {f₁ f₂ : Flush U} {L₁ L₂ : BlockId}
    (hp₁ : SupportPreferring U f₁) (hp₂ : SupportPreferring U f₂)
    (h₁ : f₁.block ρ = some L₁) (h₂ : f₂.block ρ = some L₂)
    (hex : ∃ A, IsAnchor U ρ A ∧ Supported U A ρ) : L₁ = L₂ :=
  eq_of_isAnchor_of_supported (f₁.isAnchor ρ L₁ h₁) (f₂.isAnchor ρ L₂ h₂)
    (hp₁ ρ L₁ h₁ hex) (hp₂ ρ L₂ h₂ hex)

/-- And so they agree there. -/
theorem block_eq_of_supportPreferring {f₁ f₂ : Flush U}
    (hp₁ : SupportPreferring U f₁) (hp₂ : SupportPreferring U f₂)
    (hs₁ : (f₁.block ρ).isSome) (hs₂ : (f₂.block ρ).isSome)
    (hex : ∃ A, IsAnchor U ρ A ∧ Supported U A ρ) :
    f₁.block ρ = f₂.block ρ := by
  obtain ⟨L₁, h₁⟩ := Option.isSome_iff_exists.mp hs₁
  obtain ⟨L₂, h₂⟩ := Option.isSome_iff_exists.mp hs₂
  rw [h₁, h₂, eq_of_supportPreferring hp₁ hp₂ h₁ h₂ hex]

/-! ## The strengthened descent -/

theorem descentUpto_self_gen (n : ℕ) (A : BlockId) {ρ : ℕ} (h : (U.block A).round = ρ) :
    descentSUpto U n A ρ = some A := by
  cases n <;> simp [descentSUpto, h]

theorem mem_suppAnchorsOf {A : BlockId} {s : Finset BlockId} :
    A ∈ suppAnchorsOf U s ↔ A ∈ anchorsOf U s ∧ Supported U A (U.block A).round :=
  Finset.mem_filter

theorem descendS_mem (h : descendS U B = some L) :
    L ∈ suppAnchorsOf U (strongOf U B) ∧
      (U.block L).round = maxSuppRound U (strongOf U B) :=
  Finset.mem_filter.mp (pick_mem h)

/-- **It makes a choice whenever the cone holds a supported anchor.** -/
theorem descendS_isSome (h : (suppAnchorsOf U (strongOf U B)).Nonempty) :
    (descendS U B).isSome := by
  obtain ⟨b, hb, hsup⟩ := Finset.exists_mem_eq_sup (suppAnchorsOf U (strongOf U B)) h
    (fun A => (U.block A).round)
  exact pick_isSome ⟨b, Finset.mem_filter.mpr ⟨hb, hsup.symm⟩⟩

theorem descendS_mem_ids (hB : B ∈ U.ids) (h : descendS U B = some L) : L ∈ U.ids :=
  history_subset_ids hB
    (mem_strongOf.mp (mem_anchorsOf.mp (mem_suppAnchorsOf.mp (descendS_mem h).1).1).1).2

theorem descendS_round_lt (hB : B ∈ U.ids) (h : descendS U B = some L) :
    (U.block L).round < (U.block B).round := by
  obtain ⟨hne, hhist⟩ :=
    mem_strongOf.mp (mem_anchorsOf.mp (mem_suppAnchorsOf.mp (descendS_mem h).1).1).1
  rcases Nat.lt_or_ge (U.block L).round (U.block B).round with hlt | hge
  · exact hlt
  · exact absurd (eq_of_mem_history_of_round_eq hB hhist
      (le_antisymm (round_le_of_mem_history hB hhist) hge)) hne

/-- A supported anchor of the cone is at or below the highest such
round. -/
theorem le_maxSuppRound {A : BlockId} {s : Finset BlockId}
    (h : A ∈ suppAnchorsOf U s) : (U.block A).round ≤ maxSuppRound U s :=
  Finset.le_sup (f := fun C => (U.block C).round) h

/-- A committed anchor of the cone is one of the supported anchors of
the cone. -/
theorem mem_suppAnchorsOf_of_committed {A : BlockId} {ρ : ℕ} {s : Finset BlockId}
    (hc : Committed U A ρ) (hs : A ∈ s) : A ∈ suppAnchorsOf U s := by
  refine mem_suppAnchorsOf.mpr ⟨mem_anchorsOf.mpr ⟨hs, ?_⟩, ?_⟩
  · unfold IsAnchorBlock
    rw [hc.1.2.1]
    exact hc.1.2.2
  · rw [hc.1.2.1]
    exact hc.2.1

/-- **The strengthened descent reaches every committed anchor of the
cone.** The step down cannot pass one by: a supported anchor sits at
every round the chain could land on above it, and anchor uniqueness
fixes which block each of those is. -/
theorem descentSUpto_reaches : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ n → ∀ (L : BlockId) (ρ : ℕ), Committed U L ρ →
    L ∈ strongOf U B → descentSUpto U n B ρ = some L := by
  intro n
  induction n with
  | zero =>
      intro B hB hr L ρ hc hmem
      exact absurd (lt_of_lt_of_le (by
        have := mem_strongOf.mp hmem
        rcases Nat.lt_or_ge (U.block L).round (U.block B).round with hlt | hge
        · exact hlt
        · exact absurd (eq_of_mem_history_of_round_eq hB this.2
            (le_antisymm (round_le_of_mem_history hB this.2) hge)) this.1) hr)
        (by omega)
  | succ n ih =>
      intro B hB hr L ρ hc hmem
      have hLr : (U.block L).round = ρ := hc.1.2.1
      have hlt : ρ < (U.block B).round := by
        obtain ⟨hne, hhist⟩ := mem_strongOf.mp hmem
        rcases Nat.lt_or_ge (U.block L).round (U.block B).round with h | hge
        · omega
        · exact absurd (eq_of_mem_history_of_round_eq hB hhist
            (le_antisymm (round_le_of_mem_history hB hhist) hge)) hne
      rw [descentSUpto, if_neg (by omega : ¬ ((U.block B).round = ρ))]
      obtain ⟨C, hd⟩ := Option.isSome_iff_exists.mp
        (descendS_isSome ⟨L, mem_suppAnchorsOf_of_committed hc hmem⟩)
      rw [hd, Option.bind_some]
      have hCids := descendS_mem_ids hB hd
      have hClt := descendS_round_lt hB hd
      have hCsup := (mem_suppAnchorsOf.mp (descendS_mem hd).1).2
      have hCanc : IsAnchor U (U.block C).round C :=
        ⟨hCids, rfl, (mem_anchorsOf.mp (mem_suppAnchorsOf.mp (descendS_mem hd).1).1).2⟩
      have hCge : ρ ≤ (U.block C).round := by
        rw [(descendS_mem hd).2, ← hLr]
        exact le_maxSuppRound (mem_suppAnchorsOf_of_committed hc hmem)
      rcases Nat.eq_or_lt_of_le hCge with heq | hgt
      · -- the chain has landed on `L`'s round, so it has landed on `L`
        have : C = L := by
          refine eq_of_isAnchor_of_supported (r := ρ) ?_ hc.1 ?_ hc.2.1
          · exact ⟨hCids, heq.symm, by rw [heq]; exact hCanc.2.2⟩
          · rw [heq]; exact hCsup
        rw [this, descentUpto_self_gen n L hLr]
      · -- one round further up at least: `L` is still in the new cone
        refine ih C hCids (by omega) L ρ hc ?_
        rcases Nat.eq_or_lt_of_le hgt with heq1 | hgt1
        · -- exactly one round above: `C` is the linking anchor, which cites `L`
          have heq1' : ρ + 1 = (U.block C).round := by omega
          obtain ⟨L', hL'⟩ := hc.2.2
          obtain ⟨haL', href, hsL'⟩ := mem_linkers.mp hL'
          have hCL' : C = L' := by
            refine eq_of_isAnchor_of_supported (r := ρ + 1) ?_ haL' ?_ hsL'
            · exact ⟨hCids, heq1'.symm, by rw [heq1']; exact hCanc.2.2⟩
            · rw [heq1']; exact hCsup
          rw [hCL']
          exact mem_strongOf.mpr ⟨by intro h; rw [h, haL'.2.1] at hLr; omega,
            mem_history_of_mem_refs haL'.1 href⟩
        · -- two rounds or more: propagation puts `L` in every cone up there
          exact mem_strongOf.mpr ⟨by intro h; rw [h] at hLr; omega,
            (mem_history_iff hCids).mpr (reaches_of_supported hc.2.1 hCids (by omega))⟩

/-! ## Agreement below a meeting point

The fuelled descent's bookkeeping, mirrored for `descendS`, so that a
round two records both reach the same block at carries agreement to
every round below it. -/

theorem descendS_eq_none_of_round_zero (hB : B ∈ U.ids) (h0 : (U.block B).round = 0) :
    descendS U B = none := by
  cases h : descendS U B with
  | none => rfl
  | some A =>
      exact absurd (mem_anchorsOf.mp (mem_suppAnchorsOf.mp (descendS_mem h).1).1).1
        (by rw [strongOf_eq_empty_of_round_zero hB h0]; simp)

theorem descentSUpto_round : ∀ (n : ℕ) (B : BlockId) (ρ : ℕ) (A : BlockId),
    descentSUpto U n B ρ = some A → (U.block A).round = ρ := by
  intro n
  induction n with
  | zero =>
      intro B ρ A h
      simp only [descentSUpto] at h
      split at h
      · rename_i hbr; rw [← Option.some.inj h]; exact hbr
      · exact absurd h (by simp)
  | succ n ih =>
      intro B ρ A h
      simp only [descentSUpto] at h
      split at h
      · rename_i hbr; rw [← Option.some.inj h]; exact hbr
      · cases hd : descendS U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C => rw [hd, Option.bind_some] at h; exact ih C ρ A h

theorem descentSUpto_mem_ids : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    ∀ (ρ : ℕ) (A : BlockId), descentSUpto U n B ρ = some A → A ∈ U.ids := by
  intro n
  induction n with
  | zero =>
      intro B hB ρ A h
      simp only [descentSUpto] at h
      split at h
      · rw [← Option.some.inj h]; exact hB
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB ρ A h
      simp only [descentSUpto] at h
      split at h
      · rw [← Option.some.inj h]; exact hB
      · cases hd : descendS U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            exact ih C (descendS_mem_ids hB hd) ρ A h

theorem descentSUpto_round_le : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    ∀ (ρ : ℕ) (A : BlockId), descentSUpto U n B ρ = some A →
    (U.block A).round ≤ (U.block B).round := by
  intro n
  induction n with
  | zero =>
      intro B hB ρ A h
      simp only [descentSUpto] at h
      split at h
      · rw [← Option.some.inj h]
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB ρ A h
      simp only [descentSUpto] at h
      split at h
      · rw [← Option.some.inj h]
      · cases hd : descendS U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            have := ih C (descendS_mem_ids hB hd) ρ A h
            have := descendS_round_lt hB hd
            omega

theorem descentSUpto_succ_eq : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ n → ∀ ρ, descentSUpto U n B ρ = descentSUpto U (n + 1) B ρ := by
  intro n
  induction n with
  | zero =>
      intro B hB hr ρ
      by_cases hbr : (U.block B).round = ρ
      · simp [descentSUpto, hbr]
      · simp only [descentSUpto, if_neg hbr]
        rw [descendS_eq_none_of_round_zero hB (by omega)]
        rfl
  | succ n ih =>
      intro B hB hr ρ
      by_cases hbr : (U.block B).round = ρ
      · simp [descentSUpto, hbr]
      · simp only [descentSUpto, if_neg hbr]
        cases hd : descendS U B with
        | none => rfl
        | some C =>
            simp only [Option.bind_some]
            exact ih C (descendS_mem_ids hB hd)
              (by have := descendS_round_lt hB hd; omega) ρ

theorem descentSUpto_add : ∀ (k m : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ m → ∀ ρ, descentSUpto U m B ρ = descentSUpto U (m + k) B ρ := by
  intro k
  induction k with
  | zero => intro m B _ _ ρ; rfl
  | succ k ih =>
      intro m B hB hr ρ
      rw [ih m B hB hr ρ, show m + (k + 1) = (m + k) + 1 by omega]
      exact descentSUpto_succ_eq (m + k) B hB (by omega) ρ

theorem descentSUpto_eq_of_le {m n : ℕ} (hB : B ∈ U.ids) (hr : (U.block B).round ≤ m)
    (hmn : m ≤ n) (ρ : ℕ) : descentSUpto U m B ρ = descentSUpto U n B ρ := by
  have := descentSUpto_add (n - m) m B hB hr ρ
  rwa [show m + (n - m) = n by omega] at this

theorem flushRecordS_eq (hB : B ∈ U.ids) {n : ℕ} (hn : (U.block B).round ≤ n) (ρ : ℕ) :
    flushRecordS U B ρ = descentSUpto U n B ρ :=
  descentSUpto_eq_of_le hB (le_refl _) hn ρ

theorem descentSUpto_suffix : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ n → ∀ (σ : ℕ) (M : BlockId), descentSUpto U n B σ = some M →
    ∀ ρ, ρ ≤ σ → descentSUpto U n B ρ = descentSUpto U n M ρ := by
  intro n
  induction n with
  | zero =>
      intro B hB hr σ M h ρ hρ
      simp only [descentSUpto] at h
      split at h
      · rw [← Option.some.inj h]
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB hr σ M h ρ hρ
      by_cases hbr : (U.block B).round = σ
      · rw [show M = B from (Option.some.inj (by rwa [descentSUpto, if_pos hbr] at h)).symm]
      · rw [descentSUpto, if_neg hbr] at h
        cases hd : descendS U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            have hCids := descendS_mem_ids hB hd
            have hClt := descendS_round_lt hB hd
            have hMσ : (U.block M).round = σ := descentSUpto_round n C σ M h
            have hMle : (U.block M).round ≤ (U.block C).round :=
              descentSUpto_round_le n C hCids σ M h
            have hbρ : (U.block B).round ≠ ρ := by omega
            rw [descentSUpto, if_neg hbρ, hd, Option.bind_some]
            rw [ih C hCids (by omega) σ M h ρ hρ]
            exact descentSUpto_succ_eq n M (descentSUpto_mem_ids n C hCids σ M h)
              (by omega) ρ

theorem flushRecordS_suffix (hB : B ∈ U.ids) {σ : ℕ} {M : BlockId} {ρ : ℕ}
    (h : flushRecordS U B σ = some M) (hρ : ρ ≤ σ) :
    flushRecordS U B ρ = flushRecordS U M ρ := by
  have hMids : M ∈ U.ids := descentSUpto_mem_ids _ B hB σ M h
  have hMσ : (U.block M).round = σ := descentSUpto_round _ B σ M h
  have hσle : σ ≤ (U.block B).round := by
    have := descentSUpto_round_le _ B hB σ M h
    omega
  rw [flushRecordS, descentSUpto_suffix _ B hB (le_refl _) σ M h ρ hρ]
  exact (flushRecordS_eq hMids (by omega) ρ).symm

/-- **Two strengthened descents agree below any block they both reach.** -/
theorem flushRecordS_agree {B₁ B₂ : BlockId} (h₁ : B₁ ∈ U.ids) (h₂ : B₂ ∈ U.ids)
    {σ : ℕ} {M : BlockId} {ρ : ℕ}
    (hm₁ : flushRecordS U B₁ σ = some M) (hm₂ : flushRecordS U B₂ σ = some M)
    (hρ : ρ ≤ σ) : flushRecordS U B₁ ρ = flushRecordS U B₂ ρ := by
  rw [flushRecordS_suffix h₁ hm₁ hρ, flushRecordS_suffix h₂ hm₂ hρ]

/-- **Two strengthened records with committed tops agree.** Chaining
puts the lower top in the higher's cone (BM5), BMP8 makes both descents
reach it, and the suffix property carries agreement to every round below
it. This is the composition the refutation needed and did not have. -/
theorem flushRecordS_agree_of_committed {B₁ B₂ : BlockId} {r₁ r₂ ρ : ℕ}
    (h₁ : B₁ ∈ U.ids) (h₂ : B₂ ∈ U.ids)
    (hc₁ : Committed U B₁ r₁) (hc₂ : Committed U B₂ r₂) (hr : r₁ ≤ r₂)
    (hρ : ρ ≤ r₁) : flushRecordS U B₁ ρ = flushRecordS U B₂ ρ := by
  rcases reaches_of_committed_of_le hc₁ hc₂ hr with heq | hre
  · rw [heq]
  · by_cases hbb : B₁ = B₂
    · rw [hbb]
    · have hmem : B₁ ∈ strongOf U B₂ :=
        mem_strongOf.mpr ⟨hbb, (mem_history_iff h₂).mpr hre⟩
      refine flushRecordS_agree h₁ h₂ ?_ (descentSUpto_reaches _ B₂ h₂ (le_refl _) B₁ r₁ hc₁ hmem) hρ
      rw [flushRecordS, hc₁.1.2.1]
      exact descentUpto_self_gen _ B₁ hc₁.1.2.1

end BlackMarlin

end LeanDag
