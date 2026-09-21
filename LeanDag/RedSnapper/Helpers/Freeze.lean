import LeanDag.RedSnapper.Model.Five.Freeze
import LeanDag.RedSnapper.Helpers.Five
import LeanDag.RedSnapper.Helpers.Persistence
import LeanDag.RedSnapper.Helpers.Verdict

/-!
# Computable freeze, and the frozen-stance permanence

Generated: decidable surrogates for the recovery machinery of
`Model/Five/Freeze.lean`, each pinned by an iff for universe members;
the counting lemmas for validator-set thresholds; and the proof core of
RS7 — `stance_at_of_frozen`: wherever a correct validator's marker
block is visible, its stance reads as the marker block's declaration,
because `freeze_final` makes every later own declaration a repetition.
Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

section Surrogates

variable (U : Universe Validator BlockId Tx Obj)

/-- The computable form of `Frozen`. -/
def FrozenDec (aₖ : BlockId) (id : Validator) (o : Obj) (b : BlockId) : Prop :=
  ∃ m ∈ historyIn U b, (U.block m).author = id ∧ (U.block m).freezes o = some aₖ

instance (aₖ : BlockId) (id : Validator) (o : Obj) (b : BlockId) :
    Decidable (FrozenDec U aₖ id o b) := by
  unfold FrozenDec; infer_instance

/-- The computable form of `FreezeQuorum`. -/
def FreezeQuorumDec (aₖ : BlockId) (o : Obj) (b : BlockId) : Prop :=
  quorum Validator ≤ (Finset.univ.filter fun id => FrozenDec U aₖ id o b).card

instance (aₖ : BlockId) (o : Obj) (b : BlockId) : Decidable (FreezeQuorumDec U aₖ o b) := by
  unfold FreezeQuorumDec; infer_instance

/-- The computable form of `Triggers`. -/
def TriggersDec (a : BlockId) (o : Obj) : Prop :=
  (∃ tx ∈ candidates U a o, ∃ tx' ∈ candidates U a o, tx ≠ tx') ∧
    (¬ ∃ b ∈ historyIn U a, IsFullUnlockCertDec U b o) ∧
    ¬ ∃ tx ∈ candidates U a o, ∃ b ∈ historyIn U a, IsFullCertDec U b tx

instance (a : BlockId) (o : Obj) : Decidable (TriggersDec U a o) := by
  unfold TriggersDec; infer_instance

/-- The computable form of `TriggerAt`. -/
def TriggerAtDec (A : Anchors U) (o : Obj) (i : ℕ) : Prop :=
  (∃ a, A.seq[i]? = some a ∧ TriggersDec U a o) ∧
    ∀ j < i, ∀ a, A.seq[j]? = some a → ¬ TriggersDec U a o

instance (A : Anchors U) (o : Obj) (i : ℕ) : Decidable (TriggerAtDec U A o i) := by
  unfold TriggerAtDec; infer_instance

/-- The computable form of `ResolvesFiveAt`. -/
def ResolvesFiveAtDec (A : Anchors U) (o : Obj) (i j : ℕ) : Prop :=
  TriggerAtDec U A o i ∧ i < j ∧
    (∃ aₖ, A.seq[i]? = some aₖ ∧ ∃ a, A.seq[j]? = some a ∧ FreezeQuorumDec U aₖ o a) ∧
    ∀ j' < j, ∀ aₖ, A.seq[i]? = some aₖ → ∀ a, A.seq[j']? = some a →
      ¬ FreezeQuorumDec U aₖ o a

set_option synthInstance.maxSize 4096 in
instance (A : Anchors U) (o : Obj) (i j : ℕ) : Decidable (ResolvesFiveAtDec U A o i j) := by
  unfold ResolvesFiveAtDec; infer_instance

/-- The computable form of `EligibleFive`. -/
def EligibleFiveDec (aₖ a : BlockId) (o : Obj) (tx : Tx) : Prop :=
  tx ∈ candidates U a o ∧
    half Validator ≤ (Finset.univ.filter fun id =>
      FrozenDec U aₖ id o a ∧ StanceSomeDec U id o a (Stance.ack tx)).card

instance (aₖ a : BlockId) (o : Obj) (tx : Tx) : Decidable (EligibleFiveDec U aₖ a o tx) := by
  unfold EligibleFiveDec; infer_instance

/-- The computable form of `FreezeDiscipline`. -/
def FreezeDisciplineDec : Prop :=
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, (U.block b).freezes o ≠ none → (U.block b).declares o ≠ none) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ m ∈ historyIn U b, (U.block m).author = (U.block b).author →
    ∀ o : Obj, (U.block m).freezes o ≠ none →
      (U.block b).declares o = none ∨ (U.block b).declares o = (U.block m).declares o) ∧
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), (U.block b).declares o = some (Stance.ack tx) →
      tx ∈ candidates U b o

set_option synthInstance.maxSize 4096 in
instance [Fintype Tx] [Fintype Obj] : Decidable (FreezeDisciplineDec U) := by
  unfold FreezeDisciplineDec; infer_instance

end Surrogates

variable {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- An anchor named by a lookup is a block of the universe. -/
theorem anchor_mem {A : Anchors U} {i : ℕ} {a : BlockId} (h : A.seq[i]? = some a) :
    a ∈ U.ids :=
  A.mem a (List.mem_of_getElem? h)

omit [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] F T in
/-- `AtLeastV` as a filter count. -/
theorem atLeastV_iff {k : ℕ} {P : Validator → Prop} [DecidablePred P] :
    AtLeastV k P ↔ k ≤ (Finset.univ.filter P).card := by
  constructor
  · rintro ⟨t, hP, hk⟩
    have : t ⊆ Finset.univ.filter P := fun v hv =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, hP v hv⟩
    exact hk.trans (Finset.card_le_card this)
  · intro hk
    exact ⟨Finset.univ.filter P, fun v hv => (Finset.mem_filter.mp hv).2, hk⟩

omit [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] F T in
/-- A validator threshold whose predicate avoids `S` fails when the rest
of the committee is too small to fill it. -/
theorem not_atLeastV_of_disjoint {k : ℕ} {P : Validator → Prop} {S : Finset Validator}
    (hcount : Fintype.card Validator < S.card + k)
    (havoid : ∀ v, P v → v ∉ S) : ¬ AtLeastV k P := by
  classical
  rintro ⟨t, hP, hk⟩
  have hsub : t ⊆ Sᶜ := fun v hv => Finset.mem_compl.mpr (havoid v (hP v hv))
  have hle := Finset.card_le_card hsub
  rw [Finset.card_compl] at hle
  have hSn : S.card ≤ Fintype.card Validator := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  omega

omit [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] F T in
/-- A validator threshold intersected with a set: the overlap is at
least `k + |S| − n`, and inherits the predicate. -/
theorem atLeastV_inter {k : ℕ} {P : Validator → Prop} {S : Finset Validator}
    (h : AtLeastV k P) :
    ∃ t : Finset Validator, t ⊆ S ∧ (∀ v ∈ t, P v) ∧
      k + S.card ≤ t.card + Fintype.card Validator := by
  classical
  obtain ⟨w, hP, hk⟩ := h
  refine ⟨w ∩ S, Finset.inter_subset_right,
    fun v hv => hP v (Finset.mem_inter.mp hv).1, ?_⟩
  have h1 := Finset.card_union_add_card_inter w S
  have h2 : (w ∪ S).card ≤ Fintype.card Validator := by
    simpa using Finset.card_le_card (Finset.subset_univ (w ∪ S))
  omega

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- The correct core of a parent threshold, with the witness blocks: at
least `k − f` correct authors, each with a block among the parents
satisfying the predicate, and every own block at the parents' round
satisfying it. -/
theorem correct_core_exists {C : BlockId} {k : ℕ} {P : BlockId → Prop}
    (hC : C ∈ U.ids) (h : AtLeast U k (U.block C).parents P) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧ k ≤ S.card + F.f ∧
      (∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).author = v →
        (U.block b).round + 1 = (U.block C).round → P b) ∧
      ∀ v ∈ S, ∃ q ∈ U.ids, (U.block q).author = v ∧
        (U.block q).round + 1 = (U.block C).round ∧ P q := by
  obtain ⟨t, hts, hP, hk⟩ := h
  refine ⟨authorsOf U.block t ∩ Correct, Finset.inter_subset_right, ?_, ?_, ?_⟩
  · have h1 : authorsOf U.block t ⊆ (authorsOf U.block t ∩ Correct) ∪ F.byzantine := by
      intro v hv
      by_cases hcv : v ∈ (Correct : Finset Validator)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hcv⟩)
      · exact Finset.mem_union_right _ (by simpa [Correct] using hcv)
    have h2 := Finset.card_le_card h1
    have h3 := Finset.card_union_le (authorsOf U.block t ∩ Correct) F.byzantine
    have h4 := F.card_byzantine
    omega
  · rintro v hv b hb hab hr
    obtain ⟨hva, hvc⟩ := Finset.mem_inter.mp hv
    obtain ⟨q, hq, haq⟩ := Finset.mem_image.mp hva
    have hqid : q ∈ U.ids := U.complete C hC q (hts hq)
    have hqr : (U.block q).round + 1 = (U.block C).round :=
      round_of_mem_parents hC (hts hq)
    have hbq : b = q :=
      U.no_equivocation b hb q hqid (hab.symm ▸ hvc) (by rw [hab, haq]) (by omega)
    exact hbq ▸ hP q hq
  · rintro v hv
    obtain ⟨hva, -⟩ := Finset.mem_inter.mp hv
    obtain ⟨q, hq, haq⟩ := Finset.mem_image.mp hva
    exact ⟨q, U.complete C hC q (hts hq), haq,
      round_of_mem_parents hC (hts hq), hP q hq⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] in
/-- The frozen-stance read: wherever a correct validator's marker block
is visible, its stance is the marker block's declaration. -/
theorem stance_at_of_frozen (hfd : FreezeDiscipline U) {m b : BlockId} {o : Obj}
    {aₖ : BlockId} (hm : m ∈ U.ids) (hb : b ∈ U.ids)
    (hc : (U.block m).author ∈ (Correct : Finset Validator))
    (hreach : Reaches U b m) (hfr : (U.block m).freezes o = some aₖ) :
    ∃ s, (U.block m).declares o = some s ∧
      StanceIs U (U.block m).author o b (some s) := by
  obtain ⟨sm, hsm⟩ : ∃ sm, (U.block m).declares o = some sm := by
    cases h : (U.block m).declares o with
    | none => exact absurd h (hfd.freeze_declares m hm hc o aₖ hfr)
    | some sm => exact ⟨sm, rfl⟩
  refine ⟨sm, hsm, ?_⟩
  have hdm : Declaring U (U.block m).author o b m := ⟨hm, rfl, hreach, by simp [hsm]⟩
  obtain ⟨s', hs'⟩ := stanceIs_exists (id := (U.block m).author) (o := o) hb
  cases s' with
  | none =>
      rcases hs' with hno | ⟨b₁, b₂, hL₁, hL₂, hne⟩
      · exact absurd ⟨m, hdm⟩ hno
      · exfalso
        have hr₁₂ : (U.block b₁).round = (U.block b₂).round :=
          le_antisymm (hL₂.2 b₁ hL₁.1) (hL₁.2 b₂ hL₂.1)
        exact hne (U.no_equivocation b₁ hL₁.1.1 b₂ hL₂.1.1
          (hL₁.1.2.1.symm ▸ hc) (hL₁.1.2.1.trans hL₂.1.2.1.symm) hr₁₂)
  | some v =>
      obtain ⟨e, hL, hd, hu⟩ := hs'
      have he : e ∈ U.ids := hL.1.1
      have hae : (U.block e).author = (U.block m).author := hL.1.2.1
      have hrme : (U.block m).round ≤ (U.block e).round := hL.2 m hdm
      rcases Nat.eq_or_lt_of_le hrme with heq | hlt
      · have hem : e = m :=
          U.no_equivocation e he m hm (hae ▸ hc) hae heq.symm
        have hv : v = sm := by
          have hdm' : (U.block m).declares o = some v := hem ▸ hd
          rw [hsm] at hdm'
          exact (Option.some.inj hdm').symm
        exact hv ▸ ⟨e, hL, hd, hu⟩
      · have hrem : Reaches U e m :=
          reaches_own_of_round_le he hm (hae.symm ▸ hc) hae.symm (by omega)
        rcases hfd.freeze_final e he (hae.symm ▸ hc) m hm hae.symm hrem o aₖ hfr
          with hnone | hsame
        · exact absurd hnone (by simp [hd])
        · rw [hd, hsm] at hsame
          exact (Option.some.inj hsame) ▸ ⟨e, hL, hd, hu⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] in
/-- A correct ACK stance names a candidate at the read point: the latest
declarer is a correct block, its declaration is candidate-gated, and
inclusion travels up. -/
theorem candidate_of_stance_ack (hfd : FreezeDiscipline U) {id : Validator} {o : Obj}
    {b : BlockId} {tx : Tx}
    (hcor : id ∈ (Correct : Finset Validator))
    (hst : StanceIs U id o b (some (Stance.ack tx))) : IsCandidate U b o tx := by
  obtain ⟨e, hL, hd, -⟩ := hst
  have he : e ∈ U.ids := hL.1.1
  have hae : (U.block e).author = id := hL.1.2.1
  have hcand := hfd.ack_candidate e he (hae ▸ hcor) o tx hd
  exact ⟨hcand.1, hcand.2.1, includes_mono hL.1.2.2.1 hcand.2.2⟩

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx]
  [DecidableEq Obj] F T in
/-- A validator threshold reads only the predicate. -/
theorem atLeastV_congr {k : ℕ} {P Q : Validator → Prop} (h : ∀ v, P v ↔ Q v) :
    AtLeastV k P ↔ AtLeastV k Q := by
  constructor <;> rintro ⟨t, hP, hk⟩
  · exact ⟨t, fun v hv => (h v).mp (hP v hv), hk⟩
  · exact ⟨t, fun v hv => (h v).mpr (hP v hv), hk⟩

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem frozen_iff {aₖ : BlockId} {id : Validator} {o : Obj} {b : BlockId}
    (hb : b ∈ U.ids) : Frozen U aₖ id o b ↔ FrozenDec U aₖ id o b := by
  constructor
  · rintro ⟨m, hm, ha, hr, hf⟩
    exact ⟨m, (mem_historyIn_iff hb).mpr ⟨hm, hr⟩, ha, hf⟩
  · rintro ⟨m, hm, ha, hf⟩
    obtain ⟨hmid, hr⟩ := (mem_historyIn_iff hb).mp hm
    exact ⟨m, hmid, ha, hr, hf⟩

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem freezeQuorum_iff {aₖ : BlockId} {o : Obj} {b : BlockId} (hb : b ∈ U.ids) :
    FreezeQuorum U aₖ o b ↔ FreezeQuorumDec U aₖ o b := by
  unfold FreezeQuorum FreezeQuorumDec
  rw [atLeastV_congr fun id => frozen_iff hb, atLeastV_iff]

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] in
/-- A fully certified transaction is a candidate of the certificate
block: its votes are valid and include it. -/
theorem isCandidate_of_fullCert {C : BlockId} {tx : Tx} (h : IsFullCert U C tx) :
    IsCandidate U C (T.input tx) tx := by
  obtain ⟨p, hp, hv⟩ := exists_of_atLeast quorum_pos h
  exact ⟨hv.1, rfl, includes_mono (Reaches.single hp) hv.2.1⟩

theorem triggers_iff {a : BlockId} {o : Obj} (ha : a ∈ U.ids) :
    Triggers U a o ↔ TriggersDec U a o := by
  unfold Triggers TriggersDec Conflicted
  constructor
  · rintro ⟨⟨tx, tx', hc, hc', hne⟩, hnu, hnf⟩
    refine ⟨⟨tx, (mem_candidates_iff ha).mpr hc,
      tx', (mem_candidates_iff ha).mpr hc', hne⟩, ?_, ?_⟩
    · rintro ⟨b, hb, hcert⟩
      obtain ⟨hbid, hr⟩ := (mem_historyIn_iff ha).mp hb
      exact hnu ⟨b, hbid, hr, (isFullUnlockCert_iff hbid).mpr hcert⟩
    · rintro ⟨tx'', htx'', b, hb, hcert⟩
      obtain ⟨hbid, hr⟩ := (mem_historyIn_iff ha).mp hb
      exact hnf ⟨tx'', (mem_candidates_iff ha).mp htx'', b, hbid, hr,
        (isFullCert_iff hbid).mpr hcert⟩
  · rintro ⟨⟨tx, htx, tx', htx', hne⟩, hnu, hnf⟩
    refine ⟨⟨tx, tx', (mem_candidates_iff ha).mp htx,
      (mem_candidates_iff ha).mp htx', hne⟩, ?_, ?_⟩
    · rintro ⟨b, hbid, hr, hcert⟩
      exact hnu ⟨b, (mem_historyIn_iff ha).mpr ⟨hbid, hr⟩,
        (isFullUnlockCert_iff hbid).mp hcert⟩
    · rintro ⟨tx'', hc'', b, hbid, hr, hcert⟩
      exact hnf ⟨tx'', (mem_candidates_iff ha).mpr hc'',
        b, (mem_historyIn_iff ha).mpr ⟨hbid, hr⟩, (isFullCert_iff hbid).mp hcert⟩

theorem triggerAt_iff {A : Anchors U} {o : Obj} {i : ℕ} :
    TriggerAt U A o i ↔ TriggerAtDec U A o i := by
  unfold TriggerAt TriggerAtDec
  constructor
  · rintro ⟨⟨a, hlk, ht⟩, hleast⟩
    exact ⟨⟨a, hlk, (triggers_iff (anchor_mem hlk)).mp ht⟩,
      fun j hj a' hlk' ht' =>
        hleast j hj a' hlk' ((triggers_iff (anchor_mem hlk')).mpr ht')⟩
  · rintro ⟨⟨a, hlk, ht⟩, hleast⟩
    exact ⟨⟨a, hlk, (triggers_iff (anchor_mem hlk)).mpr ht⟩,
      fun j hj a' hlk' ht' =>
        hleast j hj a' hlk' ((triggers_iff (anchor_mem hlk')).mp ht')⟩

theorem resolvesFiveAt_iff {A : Anchors U} {o : Obj} {i j : ℕ} :
    ResolvesFiveAt U A o i j ↔ ResolvesFiveAtDec U A o i j := by
  unfold ResolvesFiveAt ResolvesFiveAtDec
  rw [triggerAt_iff]
  constructor
  · rintro ⟨ht, hij, ⟨aₖ, a, hlk, hla, hq⟩, hleast⟩
    exact ⟨ht, hij, ⟨aₖ, hlk, a, hla, (freezeQuorum_iff (anchor_mem hla)).mp hq⟩,
      fun j' hj aₖ' hlk' a' hla' hq' => hleast j' hj aₖ' a' hlk' hla'
        ((freezeQuorum_iff (anchor_mem hla')).mpr hq')⟩
  · rintro ⟨ht, hij, ⟨aₖ, hlk, a, hla, hq⟩, hleast⟩
    exact ⟨ht, hij, ⟨aₖ, a, hlk, hla, (freezeQuorum_iff (anchor_mem hla)).mpr hq⟩,
      fun j' hj aₖ' a' hlk' hla' hq' => hleast j' hj aₖ' hlk' a' hla'
        ((freezeQuorum_iff (anchor_mem hla')).mp hq')⟩

theorem eligibleFive_iff {aₖ a : BlockId} {o : Obj} {tx : Tx} (ha : a ∈ U.ids) :
    EligibleFive U aₖ a o tx ↔ EligibleFiveDec U aₖ a o tx := by
  unfold EligibleFive EligibleFiveDec
  rw [mem_candidates_iff ha,
    atLeastV_congr fun id => and_congr (frozen_iff ha) (stanceSomeDec_iff ha),
    atLeastV_iff]

theorem freezeDiscipline_iff : FreezeDiscipline U ↔ FreezeDisciplineDec U := by
  constructor
  · intro h
    refine ⟨fun b hb hc o hf => ?_, fun b hb hc m hm ha o hf => ?_,
      fun b hb hc o tx hd => (mem_candidates_iff hb).mpr (h.ack_candidate b hb hc o tx hd)⟩
    · obtain ⟨aₖ, haₖ⟩ := Option.ne_none_iff_exists'.mp hf
      exact h.freeze_declares b hb hc o aₖ haₖ
    · obtain ⟨hmid, hr⟩ := (mem_historyIn_iff hb).mp hm
      obtain ⟨aₖ, haₖ⟩ := Option.ne_none_iff_exists'.mp hf
      exact h.freeze_final b hb hc m hmid ha hr o aₖ haₖ
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun b hb hc o aₖ hf => h1 b hb hc o (by simp [hf]),
      fun b hb hc m hmid ha hr o aₖ hf =>
        h2 b hb hc m ((mem_historyIn_iff hb).mpr ⟨hmid, hr⟩) ha o (by simp [hf]),
      fun b hb hc o tx hd => (mem_candidates_iff hb).mp (h3 b hb hc o tx hd)⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] in
/-- The two-direction argument of Lemma recovery-reflects: a full
certificate's correct core reads `ack tx` wherever its freeze markers
are visible — whether each member's votes preceded its marker (the
stance persists into the marker under the move rule) or followed it
(the frozen declaration is what later votes read). -/
theorem frozen_stance_eq_ack (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U)
    {C : BlockId} {tx : Tx} (hC : C ∈ U.ids) (hfull : IsFullCert U C tx) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      quorum Validator ≤ S.card + F.f ∧
      ∀ v ∈ S, ∀ (aₖ b : BlockId), b ∈ U.ids → Frozen U aₖ v (T.input tx) b →
        StanceIs U v (T.input tx) b (some (Stance.ack tx)) := by
  obtain ⟨S, hS, hk, hall, hex⟩ := correct_core_exists hC hfull
  have hρ : 0 < (U.block C).round := round_pos_of_atLeast hC quorum_pos hfull
  have hn := F.card_validators
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  have hpersist : ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).author = v →
      (U.block C).round ≤ (U.block b).round + 1 →
      StanceIs U v (T.input tx) b (some (Stance.ack tx)) := by
    intro v hv b hb hab hr
    refine stance_persists (ρ₀ := (U.block C).round - 1) hmove hS hcount
      (fun w hw e he hae hre => ?_) hv hb hab (by omega)
    exact hae ▸ (hall w hw e he hae (by omega)).2.2
  refine ⟨S, hS, hk, fun v hv aₖ b hb hfroz => ?_⟩
  obtain ⟨m, hm, ham, hrm, hfr⟩ := hfroz
  have hcm : (U.block m).author ∈ (Correct : Finset Validator) := ham.symm ▸ hS hv
  obtain ⟨s, hds, hstb⟩ := stance_at_of_frozen hfd hm hb hcm hrm hfr
  suffices hs : s = Stance.ack tx by
    subst hs
    exact ham ▸ hstb
  rcases le_or_gt (U.block C).round ((U.block m).round + 1) with hcase | hcase
  · have h1 := hpersist v hv m hm ham hcase
    have h2 : StanceIs U v (T.input tx) m (some s) :=
      ham ▸ stanceIs_self_of_declares hm hds
    exact (Option.some.inj (stanceIs_unique h2 h1))
  · obtain ⟨q, hq, haq, hqr, hfv⟩ := hex v hv
    have hcq : (U.block q).author ∈ (Correct : Finset Validator) := haq.symm ▸ hS hv
    have hrqm : Reaches U q m :=
      reaches_own_of_round_le hq hm hcq (ham.trans haq.symm) (by omega)
    obtain ⟨s', hds', hstq⟩ := stance_at_of_frozen hfd hm hq hcm hrqm hfr
    have hss : s' = s := Option.some.inj (hds' ▸ hds)
    subst hss
    have hackq : StanceIs U (U.block m).author (T.input tx) q
        (some (Stance.ack tx)) := by
      have := hfv.2.2
      rw [haq, ← ham] at this
      exact this
    exact Option.some.inj (stanceIs_unique hstq hackq)

end RedSnapper

end LeanDag
