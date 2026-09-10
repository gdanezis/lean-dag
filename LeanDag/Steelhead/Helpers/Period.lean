import LeanDag.Steelhead.Period.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Helpers — the period layer

Generated lemma infrastructure for `Period/Statement.lean`; not part of
the audit surface. Chain agreement (SH5) makes the anchor of an interval
unique across views and excludes an anchor in one view against none in
another, and the period sequence follows by induction on its derivation;
the scan ends by taking the least chain-committed round; under the clause
SH7a settles every chain verdict of an interval.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload} {I wa : ℕ} {coin : ℕ → Validator}

/-! ## Chain agreement, per round -/

/-- Two views agree on a round's chain verdict: SH5. -/
theorem chainDecided_unique (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U} {r : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : ChainDecided wa coin U V₁ r v₁)
    (h₂ : ChainDecided wa coin U V₂ r v₂) : v₁ = v₂ :=
  AnchoredRule.decided_unique (S := chainSlots coin) (MahiMahi.mahiMahiLaws (by omega)) trivial h₁
    V₂ v₂ h₂

/-- An anchor in one view is never a chain-skipped round in another. -/
theorem IntervalAnchor.not_none (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j k r : ℕ} {A : BlockId} (h : IntervalAnchor I wa coin U V₁ j k r A)
    (hn : ChainDecided wa coin U V₂ r none) : False :=
  Option.some_ne_none A (chainDecided_unique hwa h.commit hn)

/-- **The anchor is unique across views.** -/
theorem IntervalAnchor.unique (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j k r₁ r₂ : ℕ} {A₁ A₂ : BlockId} (h₁ : IntervalAnchor I wa coin U V₁ j k r₁ A₁)
    (h₂ : IntervalAnchor I wa coin U V₂ j k r₂ A₂) : r₁ = r₂ ∧ A₁ = A₂ := by
  rcases lt_trichotomy r₁ r₂ with h | h | h
  · exact absurd (h₂.below r₁ h₁.mem h₁.async h) (fun hn => h₁.not_none hwa hn)
  · subst h
    exact ⟨rfl, Option.some.inj (chainDecided_unique hwa h₁.commit h₂.commit)⟩
  · exact absurd (h₁.below r₂ h₂.mem h₂.async h) (fun hn => h₂.not_none hwa hn)

/-- An anchor in one view excludes no anchor in another. -/
theorem IntervalAnchor.not_noAnchor (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j k r : ℕ} {A : BlockId} (h : IntervalAnchor I wa coin U V₁ j k r A)
    (hn : NoAnchor I wa coin U V₂ j k) : False :=
  h.not_none hwa (hn r h.mem h.async)

/-! ## SH10a, SH10b -/

/-- **SH10a.** Induction on the derivation; the anchor is common, so is the update. -/
theorem periodAt_unique (hwa : 3 ≤ wa) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V₁ V₂ : View Validator BlockId Payload U} {j k₁ k₂ : ℕ}
    (h₁ : PeriodAt I wa coin upd k₀ U V₁ j k₁) (h₂ : PeriodAt I wa coin upd k₀ U V₂ j k₂) :
    k₁ = k₂ := by
  induction h₁ generalizing k₂ with
  | zero => cases h₂; rfl
  | anchor hp ha ih =>
    cases h₂ with
    | anchor hp' ha' =>
      obtain rfl := ih hp'
      obtain ⟨rfl, rfl⟩ := ha.unique hwa ha'
      rfl
    | keep hp' hn =>
      obtain rfl := ih hp'
      exact (ha.not_noAnchor hwa hn).elim
  | keep hp hn ih =>
    cases h₂ with
    | anchor hp' ha' =>
      obtain rfl := ih hp'
      exact (ha'.not_noAnchor hwa hn).elim
    | keep hp' _ => exact ih hp'

/-- The adaptive wavelength is at least three rounds everywhere when both waves are. -/
theorem adaptiveWave_ge {ws : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) (per : ℕ → ℕ) (r : ℕ) :
    3 ≤ adaptiveWave ws wa I per r := by
  unfold adaptiveWave periodic
  split <;> omega

/-- Intervals run in round order, so a round below `N` lies in an interval below `N`'s. -/
theorem intervalOf_mono {r N : ℕ} (h : r ≤ N) : intervalOf I r ≤ intervalOf I N :=
  Nat.div_le_div_right (Nat.sub_le_sub_right h 1)

/-- Two period sequences agreeing below `N`'s interval give one wavelength below `N`. -/
theorem adaptiveWave_congr {ws : ℕ} {per₁ per₂ : ℕ → ℕ} {N : ℕ}
    (h : ∀ j, j ≤ intervalOf I N → per₁ j = per₂ j) {r : ℕ} (hr : r ≤ N) :
    adaptiveWave ws wa I per₁ r = adaptiveWave ws wa I per₂ r := by
  unfold adaptiveWave
  rw [h _ (intervalOf_mono hr)]

section Slots

variable [S : Slots Validator]

/-- **A verdict reads the wavelength only at the rounds of the slots its derivation names.**
Those are the slot's own round and, above it, the rounds of the anchor the derivation rests on
and of the eligible slots it skipped on the way, every one of them at or below the round of a
block the anchor's candidate is. The hypothesis below is coarser than that: agreement at every
round at or below a bound `N` on the record's rounds, under which a slot proposed at or below `N`
decides alike. -/
theorem decided_congr {w₁ w₂ : ℕ → ℕ} {N : ℕ} (hN : ∀ b ∈ U.ids, (U.block b).round ≤ N)
    (hw : ∀ r, r ≤ N → w₁ r = w₂ r) {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided w₁ U V k v) :
    S.slotRound k ≤ N → Decided w₂ U V k v := by
  -- the anchor of an indirect step carries a block, so its round is under the bound too
  have hanchor : ∀ {j : ℕ} {A : BlockId}, IsLeaderBlock U j A → S.slotRound j ≤ N := by
    intro j A hA
    have := hN A hA.1
    rw [hA.2.1] at this
    exact this
  -- eligibility reads the wave at the slot's own round, which the bound covers
  have helig : ∀ {k m : ℕ}, S.slotRound k ≤ N →
      ((steelheadAnchored Validator BlockId Payload w₂).Eligible k m ↔
        (steelheadAnchored Validator BlockId Payload w₁).Eligible k m) := by
    intro k m hk
    rw [AnchoredRule.eligible_iff, AnchoredRule.eligible_iff]
    simp only [steelheadAnchored_waveAt, hw _ hk]
  induction h with
  | @directCommit k L hL hc =>
    intro hk
    refine Decided.directCommit hL ?_
    change MahiMahi.DirectCommitIn U V (w₂ (S.slotRound k)) L (S.slotRound k)
    rw [← hw _ hk]; exact hc
  | @directSkip k hs =>
    intro hk
    refine Decided.directSkip ?_
    change MahiMahi.DirectSkipIn U V (w₂ (S.slotRound k)) (S.leader k) (S.slotRound k)
    rw [← hw _ hk]; exact hs
  | @indirectCommit k j A L i hkj he hj hmid hi hemp hL hlink _ ihj ihmid =>
    intro hk
    have hjN := hanchor (AnchoredRule.isLeaderBlock_of_decided hj)
    refine Decided.indirectCommit hkj ((helig hk).mpr he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)
        (le_trans (S.mono h2.le) hjN)) hi (fun i' hi' L' hL' hl => ?_) hL ?_ (fun _ _ _ h => h)
    · refine hemp i' hi' L' hL' ?_
      change MahiMahi.CertifiedIn U (w₁ (S.slotRound k)) A L' (S.slotRound k)
      rw [hw _ hk]; exact hl
    · change MahiMahi.CertifiedIn U (w₂ (S.slotRound k)) A L (S.slotRound k)
      rw [← hw _ hk]; exact hlink
  | @indirectSkip k j A hkj he hj hmid hnone ihj ihmid =>
    intro hk
    have hjN := hanchor (AnchoredRule.isLeaderBlock_of_decided hj)
    refine Decided.indirectSkip hkj ((helig hk).mpr he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)
        (le_trans (S.mono h2.le) hjN)) (fun i hi L' hL' hl => ?_)
    refine hnone i hi L' hL' ?_
    change MahiMahi.CertifiedIn U (w₁ (S.slotRound k)) A L' (S.slotRound k)
    rw [hw _ hk]; exact hl

/-- **SH10b.** The sequences coincide below the record's top interval, so the two views run one
wavelength function on every round their derivations read, and SH2 applies to it. -/
theorem adaptive_decided_unique {ws : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) {upd : UpdateRule BlockId}
    {k₀ N : ℕ} {V₁ V₂ : View Validator BlockId Payload U} {per₁ per₂ : ℕ → ℕ}
    (hN : ∀ b ∈ U.ids, (U.block b).round ≤ N) {k : ℕ} (hk : S.slotRound k ≤ N)
    (h₁ : ∀ j, j ≤ intervalOf I N → PeriodAt I wa coin upd k₀ U V₁ j (per₁ j))
    (h₂ : ∀ j, j ≤ intervalOf I N → PeriodAt I wa coin upd k₀ U V₂ j (per₂ j))
    {v₁ v₂ : Option BlockId}
    (d₁ : Decided (adaptiveWave ws wa I per₁) U V₁ k v₁)
    (d₂ : Decided (adaptiveWave ws wa I per₂) U V₂ k v₂) : v₁ = v₂ := by
  have hper : ∀ j, j ≤ intervalOf I N → per₁ j = per₂ j :=
    fun j hj => periodAt_unique hwa (h₁ j hj) (h₂ j hj)
  have d₁' := decided_congr hN (fun r hr => adaptiveWave_congr (ws := ws) hper hr) d₁ hk
  exact AnchoredRule.decided_unique
    (steelheadLaws fun r => by have := adaptiveWave_ge (I := I) hws hwa per₂ r; omega) trivial d₁'
    V₂ v₂ d₂

end Slots

/-! ## SH10c, SH10d -/

/-- **SH10c.** The least chain-committed asynchronous round of the interval is the anchor, or
there is none and every round is chain-skipped. -/
theorem exists_periodAt_succ {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j k : ℕ} (hp : PeriodAt I wa coin upd k₀ U V j k)
    (hall : ∀ r, intervalOf I r = j → IsAsync k r → ∃ v, ChainDecided wa coin U V r v) :
    ∃ k', PeriodAt I wa coin upd k₀ U V (j + 1) k' := by
  classical
  by_cases hex : ∃ r, intervalOf I r = j ∧ IsAsync k r ∧ ∃ A, ChainDecided wa coin U V r (some A)
  · obtain ⟨hmem, hasync, A, hA⟩ := Nat.find_spec hex
    refine ⟨_, PeriodAt.anchor hp ⟨hmem, hasync, hA, fun r' hmem' hasync' hlt => ?_⟩⟩
    obtain ⟨v, hv⟩ := hall r' hmem' hasync'
    cases v with
    | none => exact hv
    | some B => exact absurd ⟨hmem', hasync', B, hv⟩ (Nat.find_min hex hlt)
  · refine ⟨k, PeriodAt.keep hp fun r hmem hasync => ?_⟩
    obtain ⟨v, hv⟩ := hall r hmem hasync
    cases v with
    | none => exact hv
    | some B => exact absurd ⟨r, hmem, hasync, B, hv⟩ hex

/-- A round of interval `j` lies at or below `(j + 1) · I`. -/
theorem le_of_intervalOf {j r : ℕ} (hI : 0 < I) (h : intervalOf I r = j) : r ≤ (j + 1) * I := by
  unfold intervalOf at h
  have := (Nat.div_lt_iff_lt_mul hI).mp (show (r - 1) / I < j + 1 by omega)
  omega

/-- Under the clause a caught-up view settles every chain verdict of interval `j`. -/
theorem chain_all_of_clause (hwa : 1 ≤ wa) (hI : 0 < I) {V : View Validator BlockId Payload U}
    {c N : ℕ} (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) {j : ℕ}
    (hN : MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N) :
    ∀ r, intervalOf I r = j → ∃ v, ChainDecided wa coin U V r v := by
  obtain ⟨b, hb, h⟩ := chainAllDecidedBelow hwa hrun hV ((j + 1) * I + 1) hN
  intro r hr
  exact h r (by have := le_of_intervalOf hI hr; omega)

/-- The horizon condition of interval `j + 1` covers interval `j`'s. -/
theorem horizon_mono {c N j : ℕ}
    (h : MahiMahi.decisionRoundAt wa ((j + 1 + 1) * I + 1 + c + wa - 1) ≤ N) :
    MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N := by
  unfold MahiMahi.decisionRoundAt at h ⊢
  have := Nat.mul_le_mul_right I (show j + 1 ≤ j + 1 + 1 by omega)
  omega

/-- **SH10d.** Induction on the interval, SH10c at each step. -/
theorem periodAt_of_clause (hwa : 1 ≤ wa) (hI : 0 < I) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) (j : ℕ)
    (hN : MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N) :
    ∃ k, PeriodAt I wa coin upd k₀ U V (j + 1) k := by
  induction j with
  | zero =>
    exact exists_periodAt_succ PeriodAt.zero fun r hr _ =>
      chain_all_of_clause hwa hI hrun hV hN r hr
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih (horizon_mono hN)
    exact exists_periodAt_succ hk fun r hr _ => chain_all_of_clause hwa hI hrun hV hN r hr

/-! ## SH10e, SH10f, SH10g -/

/-- **SH10e.** The anchor step of the sequence, its update read off the clause. -/
theorem periodAt_one_of_anchor [S : Slots Validator] {ws : ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j k r : ℕ} {A : BlockId}
    (hreset : ResetsOnStall U ws I upd)
    (hcert : ∀ (s : ℕ) (L : BlockId), intervalOf I (S.slotRound s) = j →
      ¬ IsAsync k (S.slotRound s) → IsLeaderBlock U s L →
      MahiMahi.certificates U ws L (S.slotRound s) = ∅)
    (hp : PeriodAt I wa coin upd k₀ U V j k) (hA : IntervalAnchor I wa coin U V j k r A) :
    PeriodAt I wa coin upd k₀ U V (j + 1) 1 :=
  hreset j k A hcert ▸ PeriodAt.anchor hp hA

/-- **SH10f.** The first multiple of `k` at or above the interval's first round, and the next one:
both lie in the interval, since it holds `I ≥ 2k` rounds. -/
theorem two_async_rounds {j k : ℕ} (hk : 1 ≤ k) (hI : 2 * k ≤ I) :
    ∃ r₁ r₂, r₁ < r₂ ∧ intervalOf I r₁ = j ∧ IsAsync k r₁ ∧ intervalOf I r₂ = j ∧ IsAsync k r₂ := by
  obtain ⟨q, m, hm, hqm⟩ : ∃ q m, m < k ∧ k * q + m = j * I + k :=
    ⟨(j * I + k) / k, (j * I + k) % k, Nat.mod_lt _ (by omega), Nat.div_add_mod _ _⟩
  have hmul : (j + 1) * I = j * I + I := by rw [Nat.add_mul, Nat.one_mul]
  have hsucc : k * q + k = k * (q + 1) := (Nat.mul_succ k q).symm
  refine ⟨k * q, k * q + k, by omega, ?_, Nat.mul_mod_right k q, ?_, ?_⟩
  · exact Nat.div_eq_of_lt_le (by omega) (by rw [hmul]; omega)
  · exact Nat.div_eq_of_lt_le (by omega) (by rw [hmul]; omega)
  · unfold IsAsync
    rw [hsucc]
    exact Nat.mul_mod_right k (q + 1)

/-- **SH10g.** Induction on the derivation: the initial period is in range, and the update rule
keeps it there. -/
theorem periodAt_mem_range {K : ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K) {j k : ℕ}
    (hp : PeriodAt I wa coin upd k₀ U V j k) : 1 ≤ k ∧ k ≤ K := by
  induction hp with
  | zero => exact ⟨h₀, hK⟩
  | anchor _ _ ih => exact hupd _ _ _ ih.1 ih.2
  | keep _ _ ih => exact ih

end Steelhead

end LeanDag
