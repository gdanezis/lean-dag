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

/-! ## The anchor's history, inside the view that found it

The failover reads the anchor's causal history; the validator holds a view. The two agree on what
the failover asks because the history lies inside the view: a chain-committed block is in the
view that committed it, since a certificate the view holds references a vote referencing the
candidate, and a view is closed under references. -/

/-- A certificate held in a view puts the candidate it certifies in the view. -/
theorem mem_ids_of_certificate_mem {w : ℕ} {V : View Validator BlockId Payload U} {L C : BlockId}
    {r : ℕ} (hC : C ∈ MahiMahi.certificates U w L r) (hCV : C ∈ V.ids) : L ∈ V.ids := by
  obtain ⟨-, -, hcar⟩ := mem_certificatesAt.mp hC
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hcar)
  obtain ⟨b, hb, -⟩ := mem_creatorsOf.mp hv
  obtain ⟨hbref, hvote⟩ := mem_carriedVotes.mp hb
  have hbV : b ∈ V.ids := V.complete C hCV b hbref
  exact mem_of_reaches_of_closed V.complete hbV
    ((mem_history_iff (V.subset_ids hbV)).mp (Finset.mem_filter.mp hvote.1).2.2)

/-- A committed candidate of Mahi-Mahi's relation lies in the view that committed it, whichever
route did: the direct route holds a certificate, the indirect one reaches a certificate from an
anchor the view committed. -/
theorem mem_ids_of_mahiMahi_decided {w : ℕ} {S : Slots Validator}
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (h : MahiMahi.Decided (S := S) w U V k v) : ∀ L, v = some L → L ∈ V.ids := by
  induction h with
  | @directCommit k L _ hc =>
    intro L' hL'
    obtain rfl := Option.some.inj hL'
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    exact mem_ids_of_certificate_mem hC hCV
  | directSkip _ => exact fun L h => by cases h
  | @indirectCommit k j A L i _ _ _ _ _ _ _ hlink _ ihA _ =>
    intro L' hL'
    obtain rfl := Option.some.inj hL'
    obtain ⟨C, hC, hre⟩ := hlink
    exact mem_ids_of_certificate_mem hC (mem_of_reaches_of_closed V.complete (ihA A rfl) hre)
  | indirectSkip _ _ _ _ _ _ _ => exact fun L h => by cases h

/-- The anchor of an interval lies in the view that found it. -/
theorem IntervalAnchor.mem_ids {V : View Validator BlockId Payload U} {j k r : ℕ} {A : BlockId}
    (h : IntervalAnchor I wa coin U V j k r A) : A ∈ V.ids :=
  mem_ids_of_mahiMahi_decided h.commit A rfl

/-- The causal history of a block a view holds lies inside the view. -/
theorem historyView_ids_subset {V : View Validator BlockId Payload U} {A : BlockId} (hA : A ∈ U.ids)
    (hAV : A ∈ V.ids) : (U.historyView A hA).ids ⊆ V.ids :=
  fun _ hi => mem_of_reaches_of_closed V.complete hAV ((mem_history_iff hA).mp hi)

/-! ## SH10e, SH10f, SH10g -/

section Failover

variable [S : Slots Validator] {ws : ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
  {V : View Validator BlockId Payload U} {per : ℕ → ℕ}

/-- The adaptive wavelength is at least two rounds everywhere when both waves are: what the laws
need to carry a verdict between views. -/
theorem adaptiveWave_two_le (hws : 2 ≤ ws) (hwa : 2 ≤ wa) (r : ℕ) :
    2 ≤ adaptiveWave ws wa I per r := by
  unfold adaptiveWave periodic
  split <;> omega

/-- **The failover fires at an anchored interval the view did not output.** What the view
commits of the interval, the anchor's history commits at most; what the history leaves undecided
below it, the view may have decided, but the slot the view leaves undecided the history does too.
So the failover's premise transfers from the view to the history, and the update is `1`. -/
theorem upd_eq_one_of_anchor (hws : 2 ≤ ws) (hwa : 2 ≤ wa)
    (hreset : ResetsOnNoOutput U (adaptiveWave ws wa I per) I upd) {j k r : ℕ} {A : BlockId}
    (hA : IntervalAnchor I wa coin U V j k r A)
    (hout : ∀ (s : ℕ) (L : BlockId), intervalOf I (S.slotRound s) = j →
      Decided (adaptiveWave ws wa I per) U V s (some L) →
      ∃ s', s' < s ∧ ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s' v) :
    upd j A k = 1 := by
  have hAU : A ∈ U.ids :=
    (AnchoredRule.isLeaderBlock_of_decided (S := chainSlots coin) hA.commit).1
  have hsub := historyView_ids_subset hAU hA.mem_ids
  have hmono : ∀ {t : ℕ} {v : Option BlockId},
      Decided (adaptiveWave ws wa I per) U (U.historyView A hAU) t v →
        Decided (adaptiveWave ws wa I per) U V t v :=
    fun h => AnchoredRule.decided_mono (S := S)
      (steelheadLaws (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        (adaptiveWave_two_le (I := I) (per := per) hws hwa)) trivial hsub h
  refine hreset j k A hAU fun s L hs hd => ?_
  obtain ⟨s', hlt, hund⟩ := hout s L hs (hmono hd)
  exact ⟨s', hlt, fun v hv => hund v (hmono hv)⟩

/-- **SH10e.** The anchor step of the sequence, its update read off the failover. -/
theorem periodAt_one_of_anchor (hws : 2 ≤ ws) (hwa : 2 ≤ wa)
    (hreset : ResetsOnNoOutput U (adaptiveWave ws wa I per) I upd) {j k r : ℕ} {A : BlockId}
    (hp : PeriodAt I wa coin upd k₀ U V j k) (hA : IntervalAnchor I wa coin U V j k r A)
    (hout : ∀ (s : ℕ) (L : BlockId), intervalOf I (S.slotRound s) = j →
      Decided (adaptiveWave ws wa I per) U V s (some L) →
      ∃ s', s' < s ∧ ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s' v) :
    PeriodAt I wa coin upd k₀ U V (j + 1) 1 :=
  upd_eq_one_of_anchor hws hwa hreset hA hout ▸ PeriodAt.anchor hp hA

end Failover

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

/-- **SH10h.** The wrapper answers `1` exactly where the clause asks it to. -/
theorem failover_resets [S : Slots Validator] (w : ℕ → ℕ) (upd : UpdateRule BlockId) :
    ResetsOnNoOutput U w I (failover U w I upd) := by
  intro j k A hA hout
  unfold failover
  rw [if_pos ⟨hA, hout⟩]

/-! ## SH14 -/

/-- The derivation of an interval's period ends in an anchor step or a keep step. -/
theorem PeriodAt.succ_cases {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j k' : ℕ}
    (h : PeriodAt I wa coin upd k₀ U V (j + 1) k') :
    (∃ k r A, PeriodAt I wa coin upd k₀ U V j k ∧ IntervalAnchor I wa coin U V j k r A ∧
        k' = upd j A k) ∨
      ∃ k, PeriodAt I wa coin upd k₀ U V j k ∧ NoAnchor I wa coin U V j k ∧ k' = k := by
  cases h with
  | anchor hp hA => exact Or.inl ⟨_, _, _, hp, hA, rfl⟩
  | keep hp hn => exact Or.inr ⟨_, hp, hn, rfl⟩

/-- A round past `(j + 1) · I` lies in an interval past `j`. -/
theorem le_intervalOf_of_lt {j b : ℕ} (hI : 0 < I) (h : (j + 1) * I < b) :
    j + 1 ≤ intervalOf I b := by
  unfold intervalOf
  rw [Nat.le_div_iff_mul_le hI]
  omega

section Slots

variable [S : Slots Validator] {ws : ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
  {V : View Validator BlockId Payload U} {per : ℕ → ℕ}

/-- **SH14.** If the slot is undecided, it sits below every commit of every later interval, so
the failover fires at the anchored one and the period is `1` from the next interval on, up to the
run; the run's rounds then carry wave `wa`, its coins commit their candidates directly, and the
drain (SH9) decides every slot below the run, the slot among them. -/
theorem output_liveness (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hI : 0 < I)
    (hreset : ResetsOnNoOutput U (adaptiveWave ws wa I per) I upd) {b : ℕ}
    (hper : ∀ j, j ≤ intervalOf I (b + wa - 1) → PeriodAt I wa coin upd k₀ U V j (per j))
    (hlead : ∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r)
    {s j₁ r₁ : ℕ} {A : BlockId} (hs : intervalOf I s < j₁)
    (hA : IntervalAnchor I wa coin U V j₁ (per j₁) r₁ A) (hb : (j₁ + 1) * I < b)
    (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v := by
  classical
  by_cases hdec : ∃ v, Decided (adaptiveWave ws wa I per) U V s v
  · exact hdec
  replace hdec : ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s v := fun v hv => hdec ⟨v, hv⟩
  -- the slot sits below every slot of a later interval, so none of them is output while it waits
  have hout : ∀ j, intervalOf I s < j → ∀ (t : ℕ) (L : BlockId),
      intervalOf I (S.slotRound t) = j → Decided (adaptiveWave ws wa I per) U V t (some L) →
      ∃ s', s' < t ∧ ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s' v := by
    intro j hj t L ht _
    refine ⟨s, ?_, hdec⟩
    rw [hid] at ht
    by_contra hts
    have := intervalOf_mono (I := I) (Nat.le_of_not_lt hts)
    omega
  -- the run lies in intervals past the anchored one, all of them derived
  have hbj : j₁ + 1 ≤ intervalOf I b := le_intervalOf_of_lt hI hb
  have hbN : intervalOf I b ≤ intervalOf I (b + wa - 1) := intervalOf_mono (by omega)
  -- the period is 1 from the interval after the anchored one up to the run's
  have hone : ∀ n, j₁ + 1 + n ≤ intervalOf I (b + wa - 1) → per (j₁ + 1 + n) = 1 := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact periodAt_unique hwa (hper _ hn)
        (periodAt_one_of_anchor hws (by omega) hreset (hper j₁ (by omega)) hA (hout j₁ hs))
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      change per (j₁ + 1 + n + 1) = 1
      rcases (hper (j₁ + 1 + n + 1) hn).succ_cases with ⟨k, r, A', hp, hA', hk⟩ | ⟨k, hp, _, hk⟩
      · rw [hk]
        exact upd_eq_one_of_anchor hws (by omega) hreset hA' (hout _ (by omega))
      · rw [hk]
        exact (periodAt_unique hwa hp (hper _ (by omega))).trans hprev
  -- so the run's rounds run at period 1: asynchronous, at wave wa, led by the coin
  have hper1 : ∀ i, i < wa → per (intervalOf I (b + i)) = 1 := by
    intro i hi
    have hlo : j₁ + 1 ≤ intervalOf I (b + i) := le_trans hbj (intervalOf_mono (by omega))
    have hhi : intervalOf I (b + i) ≤ intervalOf I (b + wa - 1) := intervalOf_mono (by omega)
    have h1 := hone (intervalOf I (b + i) - (j₁ + 1)) (by omega)
    rwa [show j₁ + 1 + (intervalOf I (b + i) - (j₁ + 1)) = intervalOf I (b + i) by omega] at h1
  have hwave : ∀ i, i < wa → adaptiveWave ws wa I per (b + i) = wa := by
    intro i hi
    unfold adaptiveWave
    rw [hper1 i hi]
    exact periodic_one _
  have hlead' : ∀ i, i < wa → S.leader (b + i) = coin (b + i) := by
    intro i hi
    refine hlead (b + i) ?_
    rw [hper1 i hi]
    exact Nat.mod_one _
  -- the run's candidates commit directly in a view holding their decision rounds
  have hrun : ∀ i, i < wa → ∃ L, Decided (adaptiveWave ws wa I per) U V (b + i) (some L) := by
    intro i hi
    obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hgood i hi)
    refine ⟨L, Decided.directCommit ⟨hL, by rw [hid]; exact hLr, hLc.trans (hlead' i hi).symm⟩ ?_⟩
    change MahiMahi.DirectCommitIn U V (adaptiveWave ws wa I per (S.slotRound (b + i))) L
      (S.slotRound (b + i))
    rw [hid, hwave i hi]
    refine MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_)
    unfold MahiMahi.decisionRoundAt
    omega
  -- and the drain decides everything below the run, the slot among it
  have hsb : s < b := by
    have h1 := le_of_intervalOf hI (rfl : intervalOf I s = intervalOf I s)
    have h2 : (intervalOf I s + 1) * I ≤ j₁ * I := Nat.mul_le_mul_right I hs
    have h3 : j₁ * I ≤ (j₁ + 1) * I := Nat.mul_le_mul_right I (by omega)
    omega
  exact allDecidedBelowOfRun
    (fun r => Nat.le_of_succ_le (adaptiveWave_two_le (I := I) (per := per) hws (by omega) r))
    (fun r => by unfold adaptiveWave periodic; split <;> omega) hid hrun s hsb

/-! ## SH14b -/

/-- A round strictly above `j · I` and at most `(j + 1) · I` lies in interval `j`. -/
theorem intervalOf_eq_of_mul_lt_le {j r : ℕ} (h₁ : j * I < r) (h₂ : r ≤ (j + 1) * I) :
    intervalOf I r = j := by
  unfold intervalOf
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- A round strictly above `(j + 1) · I` and at most `(j + 2) · I` lies in interval `j + 1`. -/
theorem intervalOf_eq_of_lt_le {j r : ℕ} (h₁ : (j + 1) * I < r) (h₂ : r ≤ (j + 2) * I) :
    intervalOf I r = j + 1 :=
  intervalOf_eq_of_mul_lt_le h₁ h₂

/-- Any `K` consecutive rounds hold a multiple of every period between `1` and `K`. -/
theorem exists_isAsync_of_le {k K b : ℕ} (hk : 1 ≤ k) (hK : k ≤ K) :
    ∃ i, i < K ∧ IsAsync k (b + i) := by
  refine ⟨(b + k - 1) / k * k - b, ?_, ?_⟩
  · have := Nat.div_mul_le_self (b + k - 1) k
    omega
  · have h1 := Nat.div_mul_le_self (b + k - 1) k
    have h2 := Nat.lt_div_mul_add (a := b + k - 1) hk
    unfold IsAsync
    rw [show b + ((b + k - 1) / k * k - b) = (b + k - 1) / k * k by omega]
    exact Nat.mul_mod_left _ _

omit S in
/-- A run of `d` good coins in every window holds a run of any shorter length, at a horizon
lowered by the difference, which the horizon must reach. -/
theorem unpredictableRunWithin_of_le {wa c d d' N : ℕ} (hwa : 1 ≤ wa) (hd : d' ≤ d)
    (hN : d - d' ≤ N)
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c d N) :
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c d' (N - (d - d')) := by
  intro k hk
  rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) hwa] at hk
  obtain ⟨k', h1, h2, hg⟩ := hrun k (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) hwa]
    change MahiMahi.decisionRoundAt wa (k + c + d - 1) ≤ N
    change MahiMahi.decisionRoundAt wa (k + c + d' - 1) ≤ N - (d - d') at hk
    unfold MahiMahi.decisionRoundAt at hk ⊢
    omega)
  exact ⟨k', h1, h2, fun i hi => hg i (by omega)⟩

omit S in
/-- **An interval with a chain-committed asynchronous round has an anchor** once every
asynchronous round of it has a chain verdict: the least chain-committed one. -/
theorem IntervalAnchor.of_committed {V : View Validator BlockId Payload U} {j k : ℕ}
    (hall : ∀ r, intervalOf I r = j → IsAsync k r → ∃ v, ChainDecided wa coin U V r v)
    (hex : ∃ r, intervalOf I r = j ∧ IsAsync k r ∧ ∃ A, ChainDecided wa coin U V r (some A)) :
    ∃ r A, IntervalAnchor I wa coin U V j k r A := by
  classical
  obtain ⟨hmem, hasync, A, hA⟩ := Nat.find_spec hex
  refine ⟨_, A, hmem, hasync, hA, fun r' hmem' hasync' hlt => ?_⟩
  obtain ⟨v, hv⟩ := hall r' hmem' hasync'
  cases v with
  | none => exact hv
  | some B => exact absurd ⟨hmem', hasync', B, hv⟩ (Nat.find_min hex hlt)

/-- **SH14b.** The run of `K` inside the interval after the slot's hits an asynchronous round,
whose chain commit gives the interval its anchor once SH7a has settled every chain verdict there;
the run in the next interval is the one SH14 needs. -/
theorem all_decided (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa) (hid : ∀ t, S.slotRound t = t)
    (hI : 0 < I) (hlead : ∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r)
    {K c N : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K)
    (hwaK : wa ≤ K) (hcK : c + K ≤ I) (hreset : ResetsOnNoOutput U (adaptiveWave ws wa I per) I upd)
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c K N)
    (hV : V.CoversUpto N) (hper : ∀ j, j ≤ intervalOf I N → PeriodAt I wa coin upd k₀ U V j (per j))
    (s : ℕ) (hN : MahiMahi.decisionRoundAt wa ((intervalOf I s + 2) * I + c + K) ≤ N) :
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v := by
  have hmul1 : (intervalOf I s + 1) * I = intervalOf I s * I + I := by
    rw [Nat.add_mul, Nat.one_mul]
  have hmul2 : (intervalOf I s + 2) * I = intervalOf I s * I + I + I := by
    rw [Nat.add_mul, Nat.two_mul, ← Nat.add_assoc]
  have hmul3 : (intervalOf I s + 1 + 1) * I = (intervalOf I s + 2) * I := rfl
  unfold MahiMahi.decisionRoundAt at hN
  -- every chain verdict of the interval after the slot's is settled
  have hall := chain_all_of_clause (by omega) hI
    (unpredictableRunWithin_of_le (by omega) hwaK (by omega) hrun)
    (hV.mono (Nat.sub_le _ _)) (j := intervalOf I s + 1) (by
      unfold MahiMahi.decisionRoundAt
      omega)
  -- a run of K good coins inside that interval hits one of its asynchronous rounds
  obtain ⟨k', hk1, hk2, hg⟩ := hrun ((intervalOf I s + 1) * I + 1) (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) (by omega)]
    change MahiMahi.decisionRoundAt wa ((intervalOf I s + 1) * I + 1 + c + K - 1) ≤ N
    unfold MahiMahi.decisionRoundAt
    omega)
  have hrange := periodAt_mem_range h₀ hK hupd (hper (intervalOf I s + 1) (by
    refine le_trans ?_ (intervalOf_mono (I := I) (show (intervalOf I s + 2) * I + c + K ≤ N by
      omega))
    exact le_intervalOf_of_lt hI (by omega)))
  obtain ⟨i, hi, hasync⟩ := exists_isAsync_of_le (b := k') hrange.1 hrange.2
  have hmem : intervalOf I (k' + i) = intervalOf I s + 1 :=
    intervalOf_eq_of_lt_le (by omega) (by omega)
  -- whose coin's candidate the view chain-commits directly
  obtain ⟨L, hLU, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hg i hi)
  have hL : ChainDecided wa coin U V (k' + i) (some L) :=
    MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hLU, hLr, hLc⟩
      (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono (by
        change MahiMahi.decisionRoundAt wa (k' + i) ≤ N
        unfold MahiMahi.decisionRoundAt
        omega)))
  obtain ⟨r₁, A, hA⟩ := IntervalAnchor.of_committed (fun r hr _ => hall r hr)
    ⟨k' + i, hmem, hasync, L, hL⟩
  -- the run of K in the next interval starts the run of wa SH14 needs
  obtain ⟨b, hb1, hb2, hgb⟩ := hrun ((intervalOf I s + 2) * I + 1) (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) (by omega)]
    change MahiMahi.decisionRoundAt wa ((intervalOf I s + 2) * I + 1 + c + K - 1) ≤ N
    unfold MahiMahi.decisionRoundAt
    omega)
  refine output_liveness hws hle hwa hid hI hreset (b := b) (fun j hj => hper j ?_) hlead
    (by omega) hA (by omega) (fun i hi => hgb i (by omega)) (hV.mono (by
      unfold MahiMahi.decisionRoundAt
      omega))
  exact le_trans hj (intervalOf_mono (by omega))

/-! ## SH14c -/

/-- **SH14c.** The `K` good coins opening interval `j` hit an asynchronous round, which the view
chain-commits directly; the `wa` good coins above the interval settle every chain verdict below
them (SH7c), so interval `j` has its anchor, and they are the run SH14 needs. -/
theorem output_liveness_of_runs (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hI : 0 < I)
    (hlead : ∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) {K : ℕ} (h₀ : 1 ≤ k₀)
    (hK : k₀ ≤ K) (hupd : ∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K) (hKI : K ≤ I)
    (hreset : ResetsOnNoOutput U (adaptiveWave ws wa I per) I upd) {b : ℕ}
    (hper : ∀ j', j' ≤ intervalOf I (b + wa - 1) → PeriodAt I wa coin upd k₀ U V j' (per j'))
    {s j : ℕ} (hs : intervalOf I s < j)
    (hgood : ∀ i, i < K → coin (j * I + 1 + i) ∈ MahiMahi.goodAt U wa (j * I + 1 + i))
    (hb : (j + 1) * I < b) (hgoodb : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v := by
  have hmul : (j + 1) * I = j * I + I := by rw [Nat.add_mul, Nat.one_mul]
  -- the run above settles every chain verdict of interval j
  have hall := chainAllDecidedBelowOfRun (by omega) hgoodb hV
  -- the K coins opening interval j hit one of its asynchronous rounds ...
  have hrange := periodAt_mem_range h₀ hK hupd (hper j (by
    have h1 := le_intervalOf_of_lt hI hb
    have h2 := intervalOf_mono (I := I) (show b ≤ b + wa - 1 by omega)
    omega))
  obtain ⟨i, hi, hasync⟩ := exists_isAsync_of_le (b := j * I + 1) hrange.1 hrange.2
  have hmem : intervalOf I (j * I + 1 + i) = j := intervalOf_eq_of_mul_lt_le (by omega) (by omega)
  -- ... whose candidate the view chain-commits directly
  obtain ⟨L, hLU, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hgood i hi)
  have hL : ChainDecided wa coin U V (j * I + 1 + i) (some L) :=
    MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hLU, hLr, hLc⟩
      (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono (by
        change MahiMahi.decisionRoundAt wa (j * I + 1 + i) ≤ _
        unfold MahiMahi.decisionRoundAt
        omega)))
  obtain ⟨r₁, A, hA⟩ := IntervalAnchor.of_committed
    (fun r hr _ => hall r (by have := le_of_intervalOf hI hr; omega))
    ⟨j * I + 1 + i, hmem, hasync, L, hL⟩
  exact output_liveness hws hle hwa hid hI hreset hper hlead hs hA hb hgoodb hV

end Slots

end Steelhead

end LeanDag
