import LeanDag.RedSnapper.Model.Five.Coin
import LeanDag.RedSnapper.Five.CoinSuccess.Statement
import LeanDag.RedSnapper.Helpers.Freeze

/-!
# Computable coin rounds, agreement transfer, and choice lemmas

Generated: decidable surrogates for `Model/Five/Coin.lean`; the
`AgreeUpto` transfer family (Mahi-Mahi's measurability idiom, carried to
stance reads: everything below a round-`≤ d` block lives at rounds
`≤ d`, where the two universes coincide); the witness-threshold builder
`atLeast_of_witness`; and the total-order choice lemma `exists_prio_min`
behind the recovery election's winner. Nothing here is part of the
audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

/-! ## Agreement transfer -/

section Agree

variable {U₁ U₂ : Universe Validator BlockId Tx Obj} {d : ℕ}

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
theorem AgreeUpto.symm (h : AgreeUpto U₁ U₂ d) : AgreeUpto U₂ U₁ d where
  ids i := (h.ids i).symm
  block i hi hr := by
    obtain ⟨hi₁, hr₁⟩ := (h.ids i).mpr ⟨hi, hr⟩
    exact (h.block i hi₁ hr₁).symm

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- Reachability from a block below the round is the same in both
universes: every step stays below the round, where the blocks agree. -/
theorem AgreeUpto.reaches (h : AgreeUpto U₁ U₂ d) {q i : BlockId}
    (hq : q ∈ U₁.ids) (hqr : (U₁.block q).round ≤ d) (hr : Reaches U₁ q i) :
    Reaches U₂ q i := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail i j hqi hstep ih =>
      have hi : i ∈ U₁.ids := mem_ids_of_reaches hq hqi
      have hir : (U₁.block i).round ≤ d := le_trans (round_le_of_reaches hq hqi) hqr
      have hstep' : j ∈ (U₂.block i).parents := by
        rw [← h.block i hi hir]
        exact hstep
      exact Relation.ReflTransGen.tail ih hstep'

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- The declaring blocks below a round-`≤ d` block are the same in both
universes. -/
theorem AgreeUpto.declaring_iff (h : AgreeUpto U₁ U₂ d) {id : Validator} {o : Obj}
    {b b' : BlockId} (hb : b ∈ U₁.ids) (hbr : (U₁.block b).round ≤ d) :
    Declaring U₁ id o b b' ↔ Declaring U₂ id o b b' := by
  obtain ⟨hb₂, hbr₂⟩ := (h.ids b).mp ⟨hb, hbr⟩
  constructor
  · rintro ⟨hb', ha, hre, hd⟩
    have hbr' : (U₁.block b').round ≤ d := le_trans (round_le_of_reaches hb hre) hbr
    obtain ⟨hb'₂, -⟩ := (h.ids b').mp ⟨hb', hbr'⟩
    have heq := h.block b' hb' hbr'
    exact ⟨hb'₂, heq ▸ ha, h.reaches hb hbr hre, heq ▸ hd⟩
  · rintro ⟨hb', ha, hre, hd⟩
    have hbr' : (U₂.block b').round ≤ d := le_trans (round_le_of_reaches hb₂ hre) hbr₂
    obtain ⟨hb'₁, hbr'₁⟩ := (h.ids b').mpr ⟨hb', hbr'⟩
    have heq := h.block b' hb'₁ hbr'₁
    exact ⟨hb'₁, heq ▸ ha, h.symm.reaches hb₂ hbr₂ hre, heq ▸ hd⟩

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- The stance read at a round-`≤ d` block is the same in both
universes. -/
theorem AgreeUpto.stanceIs_iff (h : AgreeUpto U₁ U₂ d) {id : Validator} {o : Obj}
    {b : BlockId} {s : Option (Stance Tx)} (hb : b ∈ U₁.ids)
    (hbr : (U₁.block b).round ≤ d) :
    StanceIs U₁ id o b s ↔ StanceIs U₂ id o b s := by
  have hblk : ∀ b', Declaring U₁ id o b b' → U₁.block b' = U₂.block b' := by
    rintro b' ⟨hb', -, hre, -⟩
    exact h.block b' hb' (le_trans (round_le_of_reaches hb hre) hbr)
  have hL : ∀ b', Latest U₁ id o b b' ↔ Latest U₂ id o b b' := by
    intro b'
    constructor
    · rintro ⟨hd, hmax⟩
      refine ⟨(h.declaring_iff hb hbr).mp hd, fun e he => ?_⟩
      have he₁ : Declaring U₁ id o b e := (h.declaring_iff hb hbr).mpr he
      rw [← hblk e he₁, ← hblk b' hd]
      exact hmax e he₁
    · rintro ⟨hd, hmax⟩
      have hd₁ : Declaring U₁ id o b b' := (h.declaring_iff hb hbr).mpr hd
      refine ⟨hd₁, fun e he => ?_⟩
      rw [hblk e he, hblk b' hd₁]
      exact hmax e ((h.declaring_iff hb hbr).mp he)
  cases s with
  | some v =>
      constructor <;> rintro ⟨e, hLe, hd, hu⟩
      · exact ⟨e, (hL e).mp hLe, hblk e hLe.1 ▸ hd,
          fun e' he' => hu e' ((hL e').mpr he')⟩
      · have hLe₁ := (hL e).mpr hLe
        exact ⟨e, hLe₁, hblk e hLe₁.1 ▸ hd, fun e' he' => hu e' ((hL e').mp he')⟩
  | none =>
      constructor <;> rintro (hno | ⟨c₁, c₂, hc₁, hc₂, hne⟩)
      · exact Or.inl fun ⟨e, he⟩ => hno ⟨e, (h.declaring_iff hb hbr).mpr he⟩
      · exact Or.inr ⟨c₁, c₂, (hL c₁).mp hc₁, (hL c₂).mp hc₂, hne⟩
      · exact Or.inl fun ⟨e, he⟩ => hno ⟨e, (h.declaring_iff hb hbr).mp he⟩
      · exact Or.inr ⟨c₁, c₂, (hL c₁).mpr hc₁, (hL c₂).mpr hc₂, hne⟩

end Agree

/-! ## Threshold and choice builders -/

variable {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] T in
/-- One witness block per validator of `H` builds an `AtLeast H.card`
threshold. -/
theorem atLeast_of_witness {k : ℕ} {s : Finset BlockId} {P : BlockId → Prop}
    {H : Finset Validator} (hk : k ≤ H.card)
    (h : ∀ v ∈ H, ∃ q ∈ s, (U.block q).author = v ∧ P q) : AtLeast U k s P := by
  classical
  choose q hqs hqa hqP using h
  refine ⟨H.attach.image fun v => q v.1 v.2, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨⟨v, hv⟩, -, rfl⟩ := Finset.mem_image.mp hb
    exact hqs v hv
  · intro b hb
    obtain ⟨⟨v, hv⟩, -, rfl⟩ := Finset.mem_image.mp hb
    exact hqP v hv
  · refine le_trans hk (Finset.card_le_card ?_)
    intro v hv
    exact Finset.mem_image.mpr ⟨q v hv,
      Finset.mem_image.mpr ⟨⟨v, hv⟩, H.mem_attach _, rfl⟩, hqa v hv⟩

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx]
  [DecidableEq Obj] F T in
/-- A nonempty finite set has a minimum under any total transitive
relation. -/
theorem exists_prio_min {α : Type*} {r : α → α → Prop} (htot : ∀ a b, r a b ∨ r b a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {s : Finset α} (hs : s.Nonempty) : ∃ m ∈ s, ∀ x ∈ s, r m x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert a t ha ih =>
      rcases t.eq_empty_or_nonempty with rfl | hne
      · refine ⟨a, Finset.mem_insert_self a ∅, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rcases htot x x with h | h <;> exact h
        · simp at hx
      · obtain ⟨m, hm, hmin⟩ := ih hne
        rcases htot a m with hh | hh
        · refine ⟨a, Finset.mem_insert_self a t, fun x hx => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · rcases htot x x with h | h <;> exact h
          · exact htrans hh (hmin x hx)
        · refine ⟨m, Finset.mem_insert_of_mem hm, fun x hx => ?_⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hh
          · exact hmin x hx

/-! ## Surrogates -/

section Surrogates

variable (U : Universe Validator BlockId Tx Obj)

/-- The computable form of `StancedAt`. -/
def StancedAtDec (o : Obj) (ρ : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ → ∃ s : Stance Tx, StanceSomeDec U (U.block b).author o b s

instance [Fintype Tx] (o : Obj) (ρ : ℕ) : Decidable (StancedAtDec U o ρ) := by
  unfold StancedAtDec; infer_instance

/-- The computable form of `CoinSuccess.HoldsAt`. -/
def HoldsAtDec (v : Validator) (o : Obj) (ρ : ℕ) (x : Stance Tx) : Prop :=
  ∀ b ∈ U.ids, (U.block b).author = v → (U.block b).round = ρ →
    StanceSomeDec U v o b x

instance (v : Validator) (o : Obj) (ρ : ℕ) (x : Stance Tx) :
    Decidable (HoldsAtDec U v o ρ x) := by
  unfold HoldsAtDec; infer_instance

/-- The computable form of `CoinSuccess.CertifiedAt`. -/
def CertifiedAtDec (o : Obj) (x : Stance Tx) (r : ℕ) : Prop :=
  ∀ C ∈ U.ids, (U.block C).author ∈ (Correct : Finset Validator) →
    (U.block C).round = r →
    match x with
    | Stance.ack tx => IsFullCertDec U C tx
    | Stance.bot => IsFullUnlockCertDec U C o

instance (o : Obj) (x : Stance Tx) (r : ℕ) : Decidable (CertifiedAtDec U o x r) := by
  unfold CertifiedAtDec
  cases x <;> infer_instance

/-- The computable form of `CoinRule`. -/
def CoinRuleDec (w : Validator) (o : Obj) (ρ : ℕ) : Prop :=
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance Tx, StanceSomeDec U (U.block b).author o p s →
      ¬ IsRefutationDec U b o s →
      StanceSomeDec U (U.block b).author o b s) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance Tx, StanceSomeDec U (U.block b).author o p s →
      IsRefutationDec U b o s →
      ∀ q ∈ (U.block b).parents, (U.block q).author = w →
      ∀ tx : Tx, StanceSomeDec U w o q (Stance.ack tx) → tx ∈ candidates U b o →
        StanceSomeDec U (U.block b).author o b (Stance.ack tx)) ∧
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance Tx, StanceSomeDec U (U.block b).author o p s →
      IsRefutationDec U b o s →
      ∀ q ∈ (U.block b).parents, (U.block q).author = w →
      StanceSomeDec U w o q Stance.bot →
        StanceSomeDec U (U.block b).author o b Stance.bot

set_option synthInstance.maxSize 8192 in
instance [Fintype Tx] (w : Validator) (o : Obj) (ρ : ℕ) :
    Decidable (CoinRuleDec U w o ρ) := by
  unfold CoinRuleDec; infer_instance

end Surrogates

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem stancedAt_iff {o : Obj} {ρ : ℕ} : StancedAt U o ρ ↔ StancedAtDec U o ρ := by
  unfold StancedAt StancedAtDec
  refine forall₂_congr fun b hb => ?_
  refine imp_congr Iff.rfl (imp_congr Iff.rfl (exists_congr fun s => ?_))
  exact stanceSomeDec_iff hb

omit [DecidableEq Tx] [DecidableEq Obj] T in
theorem holdsAt_iff {v : Validator} {o : Obj} {ρ : ℕ} {x : Stance Tx} :
    CoinSuccess.HoldsAt U v o ρ x ↔ HoldsAtDec U v o ρ x := by
  unfold CoinSuccess.HoldsAt HoldsAtDec
  refine forall₂_congr fun b hb => ?_
  exact imp_congr Iff.rfl (imp_congr Iff.rfl (stanceSomeDec_iff hb))

omit [DecidableEq Obj] in
theorem certifiedAt_iff {o : Obj} {x : Stance Tx} {r : ℕ} :
    CoinSuccess.CertifiedAt U o x r ↔ CertifiedAtDec U o x r := by
  unfold CoinSuccess.CertifiedAt CertifiedAtDec
  refine forall₂_congr fun C hC => ?_
  refine imp_congr Iff.rfl (imp_congr Iff.rfl ?_)
  cases x with
  | ack tx =>
      constructor
      · rintro (⟨tx', htx', hcert⟩ | ⟨hbad, -⟩)
        · cases htx'
          exact (isFullCert_iff hC).mp hcert
        · exact absurd hbad (by simp)
      · intro hcert
        exact Or.inl ⟨tx, rfl, (isFullCert_iff hC).mpr hcert⟩
  | bot =>
      constructor
      · rintro (⟨tx', htx', -⟩ | ⟨-, hcert⟩)
        · exact absurd htx' (by simp)
        · exact (isFullUnlockCert_iff hC).mp hcert
      · intro hcert
        exact Or.inr ⟨rfl, (isFullUnlockCert_iff hC).mpr hcert⟩

theorem coinRule_iff {w : Validator} {o : Obj} {ρ : ℕ} :
    CoinRule U w o ρ ↔ CoinRuleDec U w o ρ := by
  constructor
  · intro h
    refine ⟨fun b hb hc hr p hp hap s hst href => ?_,
      fun b hb hc hr p hp hap s hst href q hq haq tx hstw hcand => ?_,
      fun b hb hc hr p hp hap s hst href q hq haq hstw => ?_⟩
    · exact (stanceSomeDec_iff hb).mp (h.keep b hb hc hr p hp hap s
        ((stanceSomeDec_iff (U.complete b hb p hp)).mpr hst)
        (fun hr' => href ((isRefutation_iff hb).mp hr')))
    · exact (stanceSomeDec_iff hb).mp (h.adopt_ack b hb hc hr p hp hap s
        ((stanceSomeDec_iff (U.complete b hb p hp)).mpr hst)
        ((isRefutation_iff hb).mpr href) q hq haq tx
        ((stanceSomeDec_iff (U.complete b hb q hq)).mpr hstw)
        ((mem_candidates_iff hb).mp hcand))
    · exact (stanceSomeDec_iff hb).mp (h.adopt_bot b hb hc hr p hp hap s
        ((stanceSomeDec_iff (U.complete b hb p hp)).mpr hst)
        ((isRefutation_iff hb).mpr href) q hq haq
        ((stanceSomeDec_iff (U.complete b hb q hq)).mpr hstw))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun b hb hc hr p hp hap s hst href => ?_,
      fun b hb hc hr p hp hap s hst href q hq haq tx hstw hcand => ?_,
      fun b hb hc hr p hp hap s hst href q hq haq hstw => ?_⟩
    · exact (stanceSomeDec_iff hb).mpr (h1 b hb hc hr p hp hap s
        ((stanceSomeDec_iff (U.complete b hb p hp)).mp hst)
        (fun hr' => href ((isRefutation_iff hb).mpr hr')))
    · exact (stanceSomeDec_iff hb).mpr (h2 b hb hc hr p hp hap s
        ((stanceSomeDec_iff (U.complete b hb p hp)).mp hst)
        ((isRefutation_iff hb).mp href) q hq haq tx
        ((stanceSomeDec_iff (U.complete b hb q hq)).mp hstw)
        ((mem_candidates_iff hb).mpr hcand))
    · exact (stanceSomeDec_iff hb).mpr (h3 b hb hc hr p hp hap s
        ((stanceSomeDec_iff (U.complete b hb p hp)).mp hst)
        ((isRefutation_iff hb).mp href) q hq haq
        ((stanceSomeDec_iff (U.complete b hb q hq)).mp hstw))

end RedSnapper

end LeanDag
