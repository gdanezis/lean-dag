import LeanDag.Steelhead.Liveness.Statement
import LeanDag.Steelhead.Properties
import LeanDag.MahiMahi.Helpers.Liveness
import LeanDag.Properties.Derived.Descent
/-!
# Helpers — the liveness layer

Generated lemma infrastructure for `Liveness/Statement.lean`; not part of
the audit surface. SH6 is the timed bridge at Steelhead's support, with
the descent from `Indirect`; SH7 is Mahi-Mahi's descent and bridge at the
chain schedule, where the identity rounds discharge the spanning
hypothesis; SH8 is an induction on the derivation, with the arithmetic of
the residue class `k − 1` done by hand since `omega` reads no variable
modulus.
-/

namespace LeanDag

namespace Steelhead

open LeanDag.Properties SteelheadProperties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- A correct quorum is a quorum of the core's fault model. -/
theorem isQuorum_core {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) : (coreReliability Validator).IsQuorum T :=
  ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩

section Slots

variable [S : Slots Validator]

/-! ## SH6 — the synchronous route -/

/-- **The descent**, under the spanning hypothesis at each slot's own wave:
`Descends.of_indirect` at `Eligible` read as the round inequality. -/
theorem descends {w : ℕ → ℕ} (hw : ∀ r, 1 ≤ w r) {c : ℕ}
    (hspan : (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) c) :
    Descends (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)
      S c := by
  have hc : 0 < c := by
    have := (steelheadAnchored Validator BlockId Payload w).lt_of_eligible (hspan 1 0 (by omega))
    omega
  intro U V b hrun i hi
  exact Descends.of_indirect (S := S) (indirect (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) hw) hc (fun b i hi => by
      have := (steelheadAnchored Validator BlockId Payload w).eligible_iff.mp (hspan b i hi)
      simp only [steelheadAnchored_waveAt] at this
      have := hw (S.slotRound i)
      change S.slotRound i + w (S.slotRound i) ≤ S.slotRound (b + c - 1)
      omega) V b hrun i hi

/-- **SH6a.** The bridge, then Law 3, at the slot's own wave. -/
theorem commitsOfSynchrony {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N k : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hR : R ≤ S.slotRound k)
    (hN : ∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L) := by
  obtain ⟨L, hL⟩ := Timed.exists_decided_of_coverage (shSupport w) (shSupport_ofCoverage hw)
    (shSupport_commits fun r => by have := hw r; omega) (isQuorum_core hT hcard) hs hpop S V k
    hV hR hN hlead
  exact ⟨L, AnchoredRule.isLeaderBlock_of_decided hL.2.1, hL.2.1⟩

/-- **SH6b.** The timed descent below a fair run, at Steelhead's support. -/
theorem allDecidedBelowOfSynchrony {w : ℕ → ℕ} (hw : ∀ r, 3 ≤ w r) {T : Finset Validator}
    {c : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hspan : (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) c)
    (fair : FairRunOn T c) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N →
        (∀ j, j < b + c → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, Decided w U V i v := by
  obtain ⟨b, hb, hRb, h⟩ := Timed.decidedBelow_of_fairRun (shSupport w) (shSupport_ofCoverage hw)
    (shSupport_commits fun r => by have := hw r; omega)
    (descends (fun r => by have := hw r; omega) hspan) (isQuorum_core hT hcard) fair R k
  refine ⟨b, hb, hRb, fun U V N hs hpop hV hN i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hV hN i hi
  exact ⟨v, hv.2.1⟩

end Slots

/-! ## SH7 — the chain -/

/-- At the identity schedule a run of `wa` slots spans, at wave `wa`. -/
theorem chainSpansEligible {wa : ℕ} (hwa : 1 ≤ wa) (coin : ℕ → Validator) :
    (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).SpansEligible
      (S := chainSlots coin) wa := by
  have := (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).spansEligible_of_identity
    (S := chainSlots coin) (fun _ => rfl) (w := wa - 1) (fun _ => le_rfl)
  rwa [Nat.sub_add_cancel hwa] at this

/-- **SH7a.** MM3c at the chain schedule, in any view caught up to the horizon: the run's
commits are direct, and a view holding their decision rounds holds their certificates. -/
theorem chainAllDecidedBelow {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) (r : ℕ) (hr : MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun r (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) hwa]; exact hr)
  refine ⟨k', hk1, AnchoredRule.decided_below_of_run (S := chainSlots coin)
    (fun hi h => MahiMahi.exists_least (S := chainSlots coin) hi h) hwa
    (chainSpansEligible hwa coin) (Led := fun j => coin j ∈ MahiMahi.goodAt U wa j) hgood
    fun j _ hj2 hj => ?_⟩
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hj
  refine ⟨L, MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hL, hLr, hLc⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_))⟩
  change MahiMahi.decisionRoundAt wa j ≤ N
  unfold MahiMahi.decisionRoundAt at hr ⊢
  omega

/-- **SH7b.** The timed descent at Mahi-Mahi's support, at the chain schedule. -/
theorem chainAllDecidedBelowOfSynchrony {wa : ℕ} (hwa : 4 ≤ wa) (coin : ℕ → Validator)
    {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairRunOn (S := chainSlots coin) T wa)
    (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → MahiMahi.decisionRoundAt wa (b + wa - 1) ≤ N →
        ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  have hd : Descends (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) wa) (chainSlots coin) wa :=
    Descends.of_indirect (MahiMahiProperties.indirect (by omega)) (by omega)
      (fun b i hi => by change i + wa ≤ b + wa - 1; omega)
  obtain ⟨b, hb, hRb, h⟩ := Timed.decidedBelow_of_fairRun (MahiMahiProperties.mmSupport wa)
    (MahiMahiProperties.mmSupport_ofCoverage hwa) (MahiMahiProperties.mmSupport_commits (by omega))
    hd (isQuorum_core hT hcard) fair R k
  refine ⟨b, hb, hRb, fun U V N hs hpop hV hN i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hV (fun j hj => by
    change j + (wa - 1) ≤ N
    unfold MahiMahi.decisionRoundAt at hN
    omega) i hi
  exact ⟨v, hv.2.1⟩

/-! ## SH8 — the stall -/

section Stall

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}
  {V : View Validator BlockId Payload U} {ws wa k : ℕ}

/-- The wavelength at a synchronous round is `ws`. -/
theorem periodic_of_not_isAsync {r : ℕ} (h : ¬ IsAsync k r) : periodic ws wa k r = ws := by
  unfold IsAsync at h
  simp [periodic, h]

/-- The residue class `k − 1` is synchronous, at `2 ≤ k`. -/
theorem not_isAsync_of_mod {i : ℕ} (hk : 2 ≤ k) (hi : i % k = k - 1) : ¬ IsAsync k i := by
  unfold IsAsync; omega

/-- **A synchronous slot never commits** when no synchronous candidate is
certified: the direct commit and the link both need a certificate. -/
theorem not_commit_sync (hid : ∀ s, S.slotRound s = s)
    (hcert : ∀ (j : ℕ) (L : BlockId), ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    {j : ℕ} {A : BlockId} (hj : ¬ IsAsync k j)
    (h : Decided (periodic ws wa k) U V j (some A)) : False := by
  have hne : (MahiMahi.certificates U ws A j).Nonempty := by
    cases h with
    | directCommit hL hc =>
      change MahiMahi.DirectCommitIn U V (periodic ws wa k (S.slotRound j)) A (S.slotRound j) at hc
      rw [hid, periodic_of_not_isAsync hj] at hc
      exact MahiMahi.certificates_nonempty_of_directCommit
        (MahiMahi.directCommit_of_directCommitIn hc)
    | indirectCommit _ _ _ _ _ _ _ hlink _ =>
      change MahiMahi.CertifiedIn U (periodic ws wa k (S.slotRound j)) _ A (S.slotRound j) at hlink
      rw [hid, periodic_of_not_isAsync hj] at hlink
      exact MahiMahi.certificates_nonempty_of_certifiedIn hlink
  rw [hcert j A hj (AnchoredRule.isLeaderBlock_of_decided h)] at hne
  exact Finset.not_nonempty_empty hne

/-- An asynchronous round above `i + 1`, where `i ≡ k − 1`, lies a full
period above `i`: the arithmetic `omega` cannot do at a variable modulus. -/
theorem add_period_le_of_isAsync {i j : ℕ} (hk : 2 ≤ k) (hi : i % k = k - 1) (hj : IsAsync k j)
    (hij : i + 2 ≤ j) : i + k + 1 ≤ j := by
  unfold IsAsync at hj
  have hi' := Nat.div_add_mod i k
  have hj' := Nat.div_add_mod j k
  rw [hi] at hi'
  rw [hj] at hj'
  have hlt : k * (i / k + 1) < k * (j / k) := by
    have e : k * (i / k + 1) = k * (i / k) + k := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hq : i / k + 1 < j / k := Nat.lt_of_mul_lt_mul_left hlt
  have : k * (i / k + 2) ≤ k * (j / k) := Nat.mul_le_mul_left k hq
  rw [Nat.mul_add] at this
  omega

/-- **SH8.** Induction on the derivation: a class-`(k − 1)` slot's direct
verdicts are excluded outright, a synchronous anchor never commits, and an
asynchronous anchor leaves the class-`(k − 1)` slot one period up as an
eligible slot between, which must be skipped, which is the claim one
period up. -/
theorem stall (hws : 2 ≤ ws) (hk : ws ≤ k) (hid : ∀ s, S.slotRound s = s)
    (hcert : ∀ (j : ℕ) (L : BlockId), ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    (hskip : ∀ j, ¬ IsAsync k j → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j)
    {i : ℕ} (hi : i % k = k - 1) {v : Option BlockId}
    (h : Decided (periodic ws wa k) U V i v) : False := by
  have hk2 : 2 ≤ k := le_trans hws hk
  -- the middle slot of an asynchronous anchor's search is one period up
  have hmid_of_async : ∀ {i j : ℕ}, i % k = k - 1 → IsAsync k j →
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).Eligible i j →
      i < i + k ∧ i + k < j ∧
        (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).Eligible i (i + k) := by
    intro i j hi hj helig
    have hsync := not_isAsync_of_mod hk2 hi
    rw [AnchoredRule.eligible_iff] at helig ⊢
    simp only [steelheadAnchored_waveAt, hid, periodic_of_not_isAsync hsync] at helig ⊢
    have := add_period_le_of_isAsync hk2 hi hj (by omega)
    omega
  revert hi
  induction h with
  | @directCommit j L hL hc =>
    intro hi
    exact not_commit_sync hid hcert (not_isAsync_of_mod hk2 hi) (Decided.directCommit hL hc)
  | @directSkip j hs =>
    intro hi
    have hj := not_isAsync_of_mod hk2 hi
    change MahiMahi.DirectSkipIn U V (periodic ws wa k (S.slotRound j)) (S.leader j)
      (S.slotRound j) at hs
    rw [hid, periodic_of_not_isAsync hj] at hs
    exact hskip j hj hs
  | @indirectCommit i j A L _ hkj helig hj hmid _ _ _ _ _ _ ihmid =>
    intro hi
    by_cases hasync : IsAsync k j
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact not_commit_sync hid hcert hasync hj
  | @indirectSkip i j A hkj helig hj hmid _ _ ihmid =>
    intro hi
    by_cases hasync : IsAsync k j
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact not_commit_sync hid hcert hasync hj

end Stall

/-! ## SH9 — the drain -/

section Drain

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}

/-- At one slot per round, `wa` consecutive slots span eligibility at every wavelength function
bounded by `wa`. -/
theorem spansEligible_of_le {w : ℕ → ℕ} {wa : ℕ} (hwa : 1 ≤ wa) (hle : ∀ r, w r ≤ wa)
    (hid : ∀ s, S.slotRound s = s) :
    (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) wa := by
  have := (steelheadAnchored Validator BlockId Payload w).spansEligible_of_identity (S := S) hid
    (w := wa - 1) (fun r => by simp only [steelheadAnchored_waveAt]; have := hle r; omega)
  rwa [Nat.sub_add_cancel hwa] at this

/-- **SH9.** The relation's descent below a committed run, at each slot's own wave. -/
theorem allDecidedBelowOfRun {w : ℕ → ℕ} {wa : ℕ} {V : View Validator BlockId Payload U} {b : ℕ}
    (hw : ∀ r, 1 ≤ w r) (hle : ∀ r, w r ≤ wa) (hid : ∀ s, S.slotRound s = s)
    (hrun : ∀ i, i < wa → ∃ L, Decided w U V (b + i) (some L)) :
    ∀ i, i < b → ∃ v, Decided w U V i v := by
  have hwa : 1 ≤ wa := le_trans (hw 0) (hle 0)
  exact AnchoredRule.decided_below_of_run (fun hi h => exists_least hi h) hwa
    (spansEligible_of_le hwa hle hid) (Led := fun j => ∃ L, Decided w U V j (some L)) hrun
    fun j _ _ hj => hj

/-- The period-one wavelength is `wa` at every round. -/
theorem periodic_one {ws wa : ℕ} (r : ℕ) : periodic ws wa 1 r = wa := by
  simp [periodic, Nat.mod_one]

/-- **SH9b.** SH7a's argument at the output schedule: the clause names a run of `wa` committed
leaders past `r`, each committed directly in a view holding its decision round, and the run
decides everything below it (SH9). -/
theorem allDecidedBelowAtPeriodOne {ws wa : ℕ} (hwa : 1 ≤ wa) {V : View Validator BlockId Payload U}
    (hid : ∀ s, S.slotRound s = s) {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := S) U wa c wa N) (hV : V.CoversUpto N) (r : ℕ)
    (hr : MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, Decided (periodic ws wa 1) U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun r (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := S) hwa, hid]; exact hr)
  refine ⟨k', hk1, allDecidedBelowOfRun (fun r => by rw [periodic_one]; exact hwa)
    (fun r => le_of_eq (periodic_one r)) hid fun i hi => ?_⟩
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hgood i hi)
  refine ⟨L, Decided.directCommit ⟨hL, hLr, hLc⟩ ?_⟩
  change MahiMahi.DirectCommitIn U V (periodic ws wa 1 (S.slotRound (k' + i))) L
    (S.slotRound (k' + i))
  rw [periodic_one]
  refine MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_)
  rw [hid]
  unfold MahiMahi.decisionRoundAt at hr ⊢
  omega

/-- **SH9c.** Decision rounds at the periodic wavelength: `r + wa − 1` at an asynchronous round,
`r + ws − 1` at a synchronous one; the rest is arithmetic. -/
theorem asyncSlotCost {ws wa k : ℕ} (hid : ∀ s, S.slotRound s = s) (hws : 1 ≤ ws) (hwa : ws ≤ wa)
    {r : ℕ} (hr : IsAsync k r) :
    (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (S := S) r =
      (steelheadAnchored Validator BlockId Payload (fun _ => ws)).decisionRound (S := S) r +
        (wa - ws) ∧
    ∀ i, 1 ≤ i → i < k →
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (S := S) r ≤
        (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (S := S)
          (r + i) + (wa - ws - i) := by
  have hasync : periodic ws wa k r = wa := by unfold IsAsync at hr; simp [periodic, hr]
  refine ⟨?_, fun i hi hik => ?_⟩
  · unfold AnchoredRule.decisionRound
    simp only [steelheadAnchored_waveAt, hid, hasync]
    omega
  · have hsync : periodic ws wa k (r + i) = ws := by
      refine periodic_of_not_isAsync ?_
      unfold IsAsync at hr ⊢
      rw [Nat.add_mod, hr, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hik]
      omega
    unfold AnchoredRule.decisionRound
    simp only [steelheadAnchored_waveAt, hid, hasync, hsync]
    omega

end Drain

end Steelhead

end LeanDag
