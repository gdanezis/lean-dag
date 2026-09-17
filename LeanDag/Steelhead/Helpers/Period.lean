import LeanDag.Steelhead.Period.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Helpers — the period layer

Generated lemma infrastructure for `Period/Statement.lean`; not part of
the audit surface. Chain agreement (SH5) makes the anchor of an interval
unique across views and excludes an anchor in one view against none in
another; the agreed output's advance over an anchor's history is unique
and exists, since no verdict of a history lies above the anchor's round;
the period sequence follows by induction on its derivation; the scan
ends by taking the least chain-committed round; under the clause SH7a
settles every chain verdict of an interval.
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
    {j r : ℕ} {A : BlockId} (h : IntervalAnchor I wa coin U V₁ j r A)
    (hn : ChainDecided wa coin U V₂ r none) : False :=
  Option.some_ne_none A (chainDecided_unique hwa h.commit hn)

/-- **The anchor is unique across views.** -/
theorem IntervalAnchor.unique (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j r₁ r₂ : ℕ} {A₁ A₂ : BlockId} (h₁ : IntervalAnchor I wa coin U V₁ j r₁ A₁)
    (h₂ : IntervalAnchor I wa coin U V₂ j r₂ A₂) : r₁ = r₂ ∧ A₁ = A₂ := by
  rcases lt_trichotomy r₁ r₂ with h | h | h
  · exact absurd (h₂.below r₁ h₁.pos h₁.mem h) (fun hn => h₁.not_none hwa hn)
  · subst h
    exact ⟨rfl, Option.some.inj (chainDecided_unique hwa h₁.commit h₂.commit)⟩
  · exact absurd (h₁.below r₂ h₂.pos h₂.mem h) (fun hn => h₂.not_none hwa hn)

/-- An anchor in one view excludes no anchor in another. -/
theorem IntervalAnchor.not_noAnchor (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j r : ℕ} {A : BlockId} (h : IntervalAnchor I wa coin U V₁ j r A)
    (hn : NoAnchor I wa coin U V₂ j) : False :=
  h.not_none hwa (hn r h.pos h.mem)

/-- The anchor's block lies in the record. -/
theorem IntervalAnchor.mem_ids_U {V : View Validator BlockId Payload U} {j r : ℕ} {A : BlockId}
    (h : IntervalAnchor I wa coin U V j r A) : A ∈ U.ids :=
  (AnchoredRule.isLeaderBlock_of_decided (S := chainSlots coin) h.commit).1

/-- The anchor's block sits at the anchor's round. -/
theorem IntervalAnchor.round_eq {V : View Validator BlockId Payload U} {j r : ℕ} {A : BlockId}
    (h : IntervalAnchor I wa coin U V j r A) : (U.block A).round = r :=
  (AnchoredRule.isLeaderBlock_of_decided (S := chainSlots coin) h.commit).2.1

/-! ## The anchor's history, inside the view that found it

The agreed output is read in the anchor's causal history; the validator holds a view. The two
agree on what the output asks because the history lies inside the view: a chain-committed block
is in the view that committed it, since a certificate the view holds references a vote
referencing the candidate, and a view is closed under references. -/

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

/-- A committed candidate of the output relation lies in the view that committed it, by the same
two routes at the round's own wavelength. -/
theorem mem_ids_of_decided {w : ℕ → ℕ} {S : Slots Validator}
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (h : Decided (S := S) w U V k v) : ∀ L, v = some L → L ∈ V.ids := by
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
theorem IntervalAnchor.mem_ids {V : View Validator BlockId Payload U} {j r : ℕ} {A : BlockId}
    (h : IntervalAnchor I wa coin U V j r A) : A ∈ V.ids :=
  mem_ids_of_mahiMahi_decided h.commit A rfl

/-- The causal history of a block a view holds lies inside the view. -/
theorem historyView_ids_subset {V : View Validator BlockId Payload U} {A : BlockId} (hA : A ∈ U.ids)
    (hAV : A ∈ V.ids) : (U.historyView A hA).ids ⊆ V.ids :=
  fun _ hi => mem_of_reaches_of_closed V.complete hAV ((mem_history_iff hA).mp hi)

section Slots

variable [S : Slots Validator]

/-- **A verdict reads the wavelength only at the rounds of the slots its derivation names.**
Those are the slot's own round and, above it, the rounds of the anchor the derivation rests on
and of the eligible slots it skipped on the way, every one of them at or below the round of a
block the anchor's candidate is. The hypothesis below is coarser than that: agreement at every
round at or below a bound `N` on the rounds of the view's blocks, under which a slot proposed at
or below `N` decides alike. -/
theorem decided_congr {w₁ w₂ : ℕ → ℕ} {N : ℕ} {V : View Validator BlockId Payload U}
    (hN : ∀ b ∈ V.ids, (U.block b).round ≤ N) (hw : ∀ r, r ≤ N → w₁ r = w₂ r) {k : ℕ}
    {v : Option BlockId} (h : Decided w₁ U V k v) :
    S.slotRound k ≤ N → Decided w₂ U V k v := by
  -- the anchor of an indirect step is a block the view committed, so its round is under the
  -- bound too
  have hanchor : ∀ {j : ℕ} {A : BlockId}, Decided w₁ U V j (some A) → S.slotRound j ≤ N := by
    intro j A hj
    have := hN A (mem_ids_of_decided hj A rfl)
    rw [(AnchoredRule.isLeaderBlock_of_decided hj).2.1] at this
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
    have hjN := hanchor hj
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
    have hjN := hanchor hj
    refine Decided.indirectSkip hkj ((helig hk).mpr he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)
        (le_trans (S.mono h2.le) hjN)) (fun i hi L' hL' hl => ?_)
    refine hnone i hi L' hL' ?_
    change MahiMahi.CertifiedIn U (w₁ (S.slotRound k)) A L' (S.slotRound k)
    rw [hw _ hk]; exact hl

/-- **A verdict reads the wavelength only at the slots the view decides**: its own, the anchor's
and the skipped slots between, each of them decided in the view. Two wavelength functions that
agree at every slot the view decides under the first give the same verdicts. -/
theorem decided_congr_of_decided {w₁ w₂ : ℕ → ℕ} {V : View Validator BlockId Payload U}
    (hw : ∀ (r : ℕ) (v : Option BlockId), Decided w₁ U V r v →
      w₁ (S.slotRound r) = w₂ (S.slotRound r))
    {k : ℕ} {v : Option BlockId} (h : Decided w₁ U V k v) : Decided w₂ U V k v := by
  have helig : ∀ {k m : ℕ}, w₁ (S.slotRound k) = w₂ (S.slotRound k) →
      ((steelheadAnchored Validator BlockId Payload w₂).Eligible k m ↔
        (steelheadAnchored Validator BlockId Payload w₁).Eligible k m) := by
    intro k m hk
    rw [AnchoredRule.eligible_iff, AnchoredRule.eligible_iff]
    simp only [steelheadAnchored_waveAt, hk]
  induction h with
  | @directCommit k L hL hc =>
    have hk := hw k _ (Decided.directCommit hL hc)
    refine Decided.directCommit hL ?_
    change MahiMahi.DirectCommitIn U V (w₂ (S.slotRound k)) L (S.slotRound k)
    rw [← hk]; exact hc
  | @directSkip k hs =>
    have hk := hw k _ (Decided.directSkip hs)
    refine Decided.directSkip ?_
    change MahiMahi.DirectSkipIn U V (w₂ (S.slotRound k)) (S.leader k) (S.slotRound k)
    rw [← hk]; exact hs
  | @indirectCommit k j A L i hkj he hj hmid hi hemp hL hlink hleast ihj ihmid =>
    have hk := hw k _ (Decided.indirectCommit hkj he hj hmid hi hemp hL hlink hleast)
    refine Decided.indirectCommit hkj ((helig hk).mpr he) ihj
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)) hi
      (fun i' hi' L' hL' hl => ?_) hL ?_ (fun _ _ _ h => h)
    · refine hemp i' hi' L' hL' ?_
      change MahiMahi.CertifiedIn U (w₁ (S.slotRound k)) A L' (S.slotRound k)
      rw [hk]; exact hl
    · change MahiMahi.CertifiedIn U (w₂ (S.slotRound k)) A L (S.slotRound k)
      rw [← hk]; exact hlink
  | @indirectSkip k j A hkj he hj hmid hnone ihj ihmid =>
    have hk := hw k _ (Decided.indirectSkip hkj he hj hmid hnone)
    refine Decided.indirectSkip hkj ((helig hk).mpr he) ihj
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)) (fun i hi L' hL' hl => ?_)
    refine hnone i hi L' hL' ?_
    change MahiMahi.CertifiedIn U (w₁ (S.slotRound k)) A L' (S.slotRound k)
    rw [hk]; exact hl

/-! ## The agreed output over an anchor's history -/

/-- **No verdict of an anchor's history lies above the anchor's round**: a direct commit holds a
certificate of the history at the slot's decision round, a direct skip a blame at its vote round,
both at or above the slot's round and at or below the anchor's; an indirect verdict rests on an
anchor of the history at a higher slot. -/
theorem slotRound_le_of_decided_historyView {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {A : BlockId}
    (hA : A ∈ U.ids) {s : ℕ} {v : Option BlockId}
    (h : Decided w U (U.historyView A hA) s v) : S.slotRound s ≤ (U.block A).round := by
  induction h with
  | @directCommit k L _ hc =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    have hCr := (mem_certificatesAt.mp hC).2.1
    have hCA := round_le_of_mem_history hA hCV
    have := hw (S.slotRound k)
    unfold MahiMahi.decisionRoundAt at hCr
    omega
  | @directSkip k hs =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    have hqA := round_le_of_mem_history hA hqV
    have := hw (S.slotRound k)
    unfold MahiMahi.votingRound at hqr
    omega
  | @indirectCommit k j _ _ _ hkj _ _ _ _ _ _ _ _ ihj _ => exact le_trans (S.mono hkj.le) ihj
  | @indirectSkip k j _ hkj _ _ _ _ ihj _ => exact le_trans (S.mono hkj.le) ihj

/-- **No verdict of an anchor's history has its vote round above the anchor's**: a direct commit
holds a certificate of the history at the slot's decision round, a direct skip a blame at its vote
round, and an indirect verdict rests on an anchor at or above the slot's floor, whose own vote
round is bounded in turn. -/
theorem voteRound_le_of_decided_historyView {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {A : BlockId}
    (hA : A ∈ U.ids) {s : ℕ} {v : Option BlockId}
    (h : Decided w U (U.historyView A hA) s v) :
    S.slotRound s + w (S.slotRound s) - 2 ≤ (U.block A).round := by
  induction h with
  | @directCommit k L _ hc =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    have hCr := (mem_certificatesAt.mp hC).2.1
    have hCA := round_le_of_mem_history hA hCV
    have := hw (S.slotRound k)
    unfold MahiMahi.decisionRoundAt at hCr
    omega
  | @directSkip k hs =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    have hqA := round_le_of_mem_history hA hqV
    have := hw (S.slotRound k)
    unfold MahiMahi.votingRound at hqr
    omega
  | @indirectCommit k j _ _ _ _ he _ _ _ _ _ _ _ ihj _ =>
    rw [AnchoredRule.eligible_iff] at he
    simp only [steelheadAnchored_waveAt] at he
    have := hw (S.slotRound k)
    have := hw (S.slotRound j)
    omega
  | @indirectSkip k j _ _ he _ _ _ ihj _ =>
    rw [AnchoredRule.eligible_iff] at he
    simp only [steelheadAnchored_waveAt] at he
    have := hw (S.slotRound k)
    have := hw (S.slotRound j)
    omega

/-- **The advance is unique**: the new cursor is the least undecided slot at or past the old one,
and the last commit is the old one or the highest commit consumed. -/
theorem AgreedAdvance.unique {w : ℕ → ℕ} {A : BlockId} {hA : A ∈ U.ids}
    {next last next₁ next₂ last₁ last₂ : ℕ}
    (h₁ : AgreedAdvance U w A hA next next₁ last last₁)
    (h₂ : AgreedAdvance U w A hA next next₂ last last₂) : next₁ = next₂ ∧ last₁ = last₂ := by
  have hn : next₁ = next₂ := by
    rcases lt_trichotomy next₁ next₂ with h | h | h
    · obtain ⟨v, hv⟩ := h₂.decided next₁ h₁.le h
      exact absurd hv (h₁.stuck v)
    · exact h
    · obtain ⟨v, hv⟩ := h₁.decided next₂ h₂.le h
      exact absurd hv (h₂.stuck v)
  subst hn
  refine ⟨rfl, le_antisymm ?_ ?_⟩
  · rcases h₁.last_mem with h | ⟨s, L, hs₁, hs₂, hd, hs⟩
    · rw [h]; exact h₂.last_ge
    · rw [← hs]; exact h₂.last_le s L hs₁ hs₂ hd
  · rcases h₂.last_mem with h | ⟨s, L, hs₁, hs₂, hd, hs⟩
    · rw [h]; exact h₁.last_ge
    · rw [← hs]; exact h₁.last_le s L hs₁ hs₂ hd

/-- **The advance exists**, from any cursor and last commit: some slot above the anchor's round is
undecided in the history, so the least undecided slot at or past the cursor exists, and the last
commit is the larger of the old one and the highest commit consumed. -/
theorem AgreedAdvance.exists {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {A : BlockId} (hA : A ∈ U.ids)
    (next last : ℕ) : ∃ next' last', AgreedAdvance U w A hA next next' last last' := by
  classical
  have hex : ∃ s, next ≤ s ∧ ∀ v, ¬ Decided w U (U.historyView A hA) s v := by
    obtain ⟨t, ht⟩ := S.unbounded ((U.block A).round + 1)
    refine ⟨max t next, le_max_right _ _, fun v hv => ?_⟩
    have h₁ := slotRound_le_of_decided_historyView hw hA hv
    have h₂ := S.mono (le_max_left t next)
    omega
  have hspec := Nat.find_spec hex
  set T := (Finset.Ico next (Nat.find hex)).filter
    fun s => ∃ L, Decided w U (U.historyView A hA) s (some L) with hT
  refine ⟨Nat.find hex, max last (T.sup S.slotRound), hspec.1, ?_, hspec.2, le_max_left _ _, ?_,
    ?_⟩
  · intro s hs₁ hs₂
    by_contra hcon
    exact Nat.find_min hex hs₂ ⟨hs₁, fun v hv => hcon ⟨v, hv⟩⟩
  · intro s L hs₁ hs₂ hd
    exact le_trans (Finset.le_sup (f := S.slotRound)
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hs₁, hs₂⟩, L, hd⟩)) (le_max_right _ _)
  · by_cases hle : T.sup S.slotRound ≤ last
    · exact Or.inl (max_eq_left hle)
    · right
      have hne : T.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Finset.sup_empty] at hle
        exact hle (Nat.zero_le _)
      obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup T hne S.slotRound
      obtain ⟨hs', L, hd⟩ := Finset.mem_filter.mp hs
      exact ⟨s, L, (Finset.mem_Ico.mp hs').1, (Finset.mem_Ico.mp hs').2, hd,
        by rw [max_eq_right (not_le.mp hle).le, hsup]⟩

/-- **The advance reads the wavelength at or below the anchor's round only**: every verdict it
reads is at a slot of the anchor's history, or refuted there, and the history holds no block above
the anchor's round; so two wavelength functions agreeing up to that round give one advance. -/
theorem AgreedAdvance.congr {w₁ w₂ : ℕ → ℕ} (hw₁ : ∀ r, 2 ≤ w₁ r) (hw₂ : ∀ r, 2 ≤ w₂ r)
    {A : BlockId} (hA : A ∈ U.ids) (hw : ∀ r, r ≤ (U.block A).round → w₁ r = w₂ r)
    {next next' last last' : ℕ} (h : AgreedAdvance U w₁ A hA next next' last last') :
    AgreedAdvance U w₂ A hA next next' last last' := by
  have hN : ∀ b ∈ (U.historyView A hA).ids, (U.block b).round ≤ (U.block A).round :=
    fun b hb => round_le_of_mem_history hA hb
  have fwd : ∀ {s : ℕ} {v : Option BlockId}, Decided w₁ U (U.historyView A hA) s v →
      Decided w₂ U (U.historyView A hA) s v :=
    fun hd => decided_congr hN hw hd (slotRound_le_of_decided_historyView hw₁ hA hd)
  have bwd : ∀ {s : ℕ} {v : Option BlockId}, Decided w₂ U (U.historyView A hA) s v →
      Decided w₁ U (U.historyView A hA) s v :=
    fun hd => decided_congr hN (fun r hr => (hw r hr).symm) hd
      (slotRound_le_of_decided_historyView hw₂ hA hd)
  exact ⟨h.le, fun s hs₁ hs₂ => (h.decided s hs₁ hs₂).imp fun _ hv => fwd hv,
    fun v hv => h.stuck v (bwd hv), h.last_ge, fun s L hs₁ hs₂ hd => h.last_le s L hs₁ hs₂ (bwd hd),
    h.last_mem.imp id fun ⟨s, L, hs₁, hs₂, hd, hs⟩ => ⟨s, L, hs₁, hs₂, fwd hd, hs⟩⟩

/-! ## SH10a, SH10b -/

/-- **Agreement of the state under two wavelengths** that agree up to the round of every anchor
one of the views finds below the interval: induction on the derivation; the anchor is common, the
advances over its history agree, so does the failover's test and the update. -/
theorem periodAt_unique_of_w (hwa : 3 ≤ wa) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V₁ V₂ : View Validator BlockId Payload U} {w₁ w₂ : ℕ → ℕ} (hw₁ : ∀ r, 2 ≤ w₁ r)
    (hw₂ : ∀ r, 2 ≤ w₂ r) {j : ℕ} {st₁ st₂ : ScanState}
    (h₁ : PeriodAt I wa coin upd k₀ U V₁ w₁ j st₁) (h₂ : PeriodAt I wa coin upd k₀ U V₂ w₂ j st₂)
    (hw : ∀ j' r A, j' < j → IntervalAnchor I wa coin U V₁ j' r A →
      ∀ ρ, ρ ≤ r → w₁ ρ = w₂ ρ) :
    st₁ = st₂ := by
  induction h₁ generalizing st₂ with
  | zero => cases h₂; rfl
  | @anchor j r next' last' st A hA hp ha hadv ih =>
    cases h₂ with
    | @anchor _ r₂ next₂ last₂ st₂ A₂ hA₂ hp' ha' hadv' =>
      obtain rfl := ih hp' fun j' r A hj => hw j' r A (by omega)
      obtain ⟨rfl, rfl⟩ := ha.unique hwa ha'
      have hadv₂ := hadv.congr hw₁ hw₂ hA (fun ρ hρ => hw j r A (by omega) ha ρ (by
        rw [ha.round_eq] at hρ; exact hρ))
      obtain ⟨rfl, rfl⟩ := hadv₂.unique hadv'
      rfl
    | keep hp' hn =>
      obtain rfl := ih hp' fun j' r A hj => hw j' r A (by omega)
      exact (ha.not_noAnchor hwa hn).elim
  | keep hp hn ih =>
    cases h₂ with
    | anchor hp' ha' _ =>
      obtain rfl := ih hp' fun j' r A hj => hw j' r A (by omega)
      exact (ha'.not_noAnchor hwa hn).elim
    | keep hp' _ => exact ih hp' fun j' r A hj => hw j' r A (by omega)

/-- **SH10a.** Both views read the agreed output at one wavelength. -/
theorem periodAt_unique (hwa : 3 ≤ wa) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V₁ V₂ : View Validator BlockId Payload U} {w : ℕ → ℕ} {j : ℕ} {st₁ st₂ : ScanState}
    (h₁ : PeriodAt I wa coin upd k₀ U V₁ w j st₁) (h₂ : PeriodAt I wa coin upd k₀ U V₂ w j st₂) :
    st₁ = st₂ := by
  induction h₁ generalizing st₂ with
  | zero => cases h₂; rfl
  | @anchor j r next' last' st A hA hp ha hadv ih =>
    cases h₂ with
    | @anchor _ r₂ next₂ last₂ st₂ A₂ hA₂ hp' ha' hadv' =>
      obtain rfl := ih hp'
      obtain ⟨rfl, rfl⟩ := ha.unique hwa ha'
      obtain ⟨rfl, rfl⟩ := hadv.unique hadv'
      rfl
    | keep hp' hn =>
      obtain rfl := ih hp'
      exact (ha.not_noAnchor hwa hn).elim
  | keep hp hn ih =>
    cases h₂ with
    | anchor hp' ha' _ =>
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

/-- **SH10b, the sequences.** Two views that derived the state of every interval below `N`'s,
each reading its agreed output at its own adaptive wavelength, derived the same periods there, by
strong induction on the interval: the anchors of the intervals below an interval lie in the
record, their histories are read at rounds below their own, where the sequences already agree, so
the two views advance the agreed output alike at every one of them and derive the same state. -/
theorem adaptive_periods_agree {ws : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) {upd : UpdateRule BlockId}
    {k₀ N : ℕ} {V₁ V₂ : View Validator BlockId Payload U} {per₁ per₂ : ℕ → ℕ}
    (h₁ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V₁ (adaptiveWave ws wa I per₁) j st ∧ per₁ j = st.period)
    (h₂ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V₂ (adaptiveWave ws wa I per₂) j st ∧ per₂ j = st.period) :
    ∀ j, j ≤ intervalOf I N → per₁ j = per₂ j := by
  have hw₁ : ∀ r, 2 ≤ adaptiveWave ws wa I per₁ r :=
    fun r => by have := adaptiveWave_ge (I := I) hws hwa per₁ r; omega
  have hw₂ : ∀ r, 2 ≤ adaptiveWave ws wa I per₂ r :=
    fun r => by have := adaptiveWave_ge (I := I) hws hwa per₂ r; omega
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  obtain ⟨st₁, hp₁, he₁⟩ := h₁ j hj
  obtain ⟨st₂, hp₂, he₂⟩ := h₂ j hj
  rw [he₁, he₂]
  refine congrArg ScanState.period
    (periodAt_unique_of_w hwa hw₁ hw₂ hp₁ hp₂ fun j' r A hj' hA ρ hρ => ?_)
  refine adaptiveWave_congr (ws := ws) (N := r) (fun j'' hj'' => ?_) hρ
  rw [hA.mem] at hj''
  exact ih j'' (by omega) (by omega)

/-- **SH10b, the verdicts.** The two views run one wavelength function on every round their
derivations read, since the sequences agree below `N`'s interval (`adaptive_periods_agree`), and
SH2 applies to it. -/
theorem adaptive_decided_unique {ws : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) {upd : UpdateRule BlockId}
    {k₀ N : ℕ} {V₁ V₂ : View Validator BlockId Payload U} {per₁ per₂ : ℕ → ℕ}
    (hN : ∀ b ∈ U.ids, (U.block b).round ≤ N) {k : ℕ} (hk : S.slotRound k ≤ N)
    (h₁ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V₁ (adaptiveWave ws wa I per₁) j st ∧ per₁ j = st.period)
    (h₂ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V₂ (adaptiveWave ws wa I per₂) j st ∧ per₂ j = st.period)
    {v₁ v₂ : Option BlockId}
    (d₁ : Decided (adaptiveWave ws wa I per₁) U V₁ k v₁)
    (d₂ : Decided (adaptiveWave ws wa I per₂) U V₂ k v₂) : v₁ = v₂ := by
  have hper := adaptive_periods_agree hws hwa h₁ h₂
  have d₁' := decided_congr (fun b hb => hN b (V₁.subset_ids hb))
    (fun r hr => adaptiveWave_congr (ws := ws) hper hr) d₁ hk
  exact AnchoredRule.decided_unique
    (steelheadLaws fun r => by have := adaptiveWave_ge (I := I) hws hwa per₂ r; omega) trivial d₁'
    V₂ v₂ d₂

/-! ## SH10c, SH10d -/

omit S in
/-- **An interval with a chain-committed round has an anchor** once every scanned round of it has
a chain verdict: the least chain-committed one. -/
theorem IntervalAnchor.of_committed {V : View Validator BlockId Payload U} {j : ℕ}
    (hall : ∀ r, 1 ≤ r → intervalOf I r = j → ∃ v, ChainDecided wa coin U V r v)
    (hex : ∃ r, 1 ≤ r ∧ intervalOf I r = j ∧ ∃ A, ChainDecided wa coin U V r (some A)) :
    ∃ r A, IntervalAnchor I wa coin U V j r A := by
  classical
  obtain ⟨hpos, hmem, A, hA⟩ := Nat.find_spec hex
  refine ⟨_, A, hpos, hmem, hA, fun r' hpos' hmem' hlt => ?_⟩
  obtain ⟨v, hv⟩ := hall r' hpos' hmem'
  cases v with
  | none => exact hv
  | some B => exact absurd ⟨hpos', hmem', B, hv⟩ (Nat.find_min hex hlt)

/-- **SH10c.** The least chain-committed round of the interval is the anchor, over whose history
the agreed output advances, or there is none and every scanned round is chain-skipped. -/
theorem exists_periodAt_succ {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j : ℕ} {st : ScanState}
    (hp : PeriodAt I wa coin upd k₀ U V w j st)
    (hall : ∀ r, 1 ≤ r → intervalOf I r = j → ∃ v, ChainDecided wa coin U V r v) :
    ∃ st', PeriodAt I wa coin upd k₀ U V w (j + 1) st' := by
  classical
  by_cases hex : ∃ r, 1 ≤ r ∧ intervalOf I r = j ∧ ∃ A, ChainDecided wa coin U V r (some A)
  · obtain ⟨r, A, hA⟩ := IntervalAnchor.of_committed hall hex
    obtain ⟨next', last', hadv⟩ := AgreedAdvance.exists hw hA.mem_ids_U st.next st.lastCommit
    exact ⟨_, PeriodAt.anchor hp hA hadv⟩
  · refine ⟨st, PeriodAt.keep hp fun r hpos hmem => ?_⟩
    obtain ⟨v, hv⟩ := hall r hpos hmem
    cases v with
    | none => exact hv
    | some B => exact absurd ⟨r, hpos, hmem, B, hv⟩ hex

omit S in
/-- A round of interval `j` lies at or below `(j + 1) · I`. -/
theorem le_of_intervalOf {j r : ℕ} (hI : 0 < I) (h : intervalOf I r = j) : r ≤ (j + 1) * I := by
  unfold intervalOf at h
  have := (Nat.div_lt_iff_lt_mul hI).mp (show (r - 1) / I < j + 1 by omega)
  omega

omit S in
/-- Under the clause a caught-up view settles every chain verdict of interval `j`. -/
theorem chain_all_of_clause (hwa : 1 ≤ wa) (hI : 0 < I) {V : View Validator BlockId Payload U}
    {c N : ℕ} (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) {j : ℕ}
    (hN : MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N) :
    ∀ r, intervalOf I r = j → ∃ v, ChainDecided wa coin U V r v := by
  obtain ⟨b, hb, h⟩ := chainAllDecidedBelow hwa hrun hV ((j + 1) * I + 1) hN
  intro r hr
  exact h r (by have := le_of_intervalOf hI hr; omega)

omit S in
/-- The horizon condition of interval `j + 1` covers interval `j`'s. -/
theorem horizon_mono {c N j : ℕ}
    (h : MahiMahi.decisionRoundAt wa ((j + 1 + 1) * I + 1 + c + wa - 1) ≤ N) :
    MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N := by
  unfold MahiMahi.decisionRoundAt at h ⊢
  have := Nat.mul_le_mul_right I (show j + 1 ≤ j + 1 + 1 by omega)
  omega

/-- **SH10d.** Induction on the interval, SH10c at each step. -/
theorem periodAt_of_clause (hwa : 1 ≤ wa) (hI : 0 < I) {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r)
    {upd : UpdateRule BlockId} {k₀ : ℕ} {V : View Validator BlockId Payload U} {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) (j : ℕ)
    (hN : MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N) :
    ∃ st, PeriodAt I wa coin upd k₀ U V w (j + 1) st := by
  induction j with
  | zero =>
    exact exists_periodAt_succ hw PeriodAt.zero fun r _ hr =>
      chain_all_of_clause hwa hI hrun hV hN r hr
  | succ j ih =>
    obtain ⟨st, hst⟩ := ih (horizon_mono hN)
    exact exists_periodAt_succ hw hst fun r _ hr => chain_all_of_clause hwa hI hrun hV hN r hr

/-! ## SH10e, SH10f, SH10g -/

/-- **SH10e.** The anchor step of the sequence, its test read off. -/
theorem periodAt_one_of_anchor {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j r next' last' : ℕ} {st : ScanState} {A : BlockId}
    {hA : A ∈ U.ids} (hp : PeriodAt I wa coin upd k₀ U V w j st)
    (ha : IntervalAnchor I wa coin U V j r A)
    (hadv : AgreedAdvance U w A hA st.next next' st.lastCommit last') (h : last' + I < r) :
    PeriodAt I wa coin upd k₀ U V w (j + 1) ⟨1, next', last'⟩ := by
  have := PeriodAt.anchor hp ha hadv
  rwa [if_pos h] at this

omit S in
/-- A round of an interval past the first lies above the interval's first round less one. -/
theorem mul_add_one_le_of_intervalOf {j r : ℕ} (hI : 0 < I) (hj : 1 ≤ j)
    (h : intervalOf I r = j) : j * I + 1 ≤ r := by
  unfold intervalOf at h
  have := (Nat.le_div_iff_mul_le hI).mp (le_of_eq h.symm)
  have : 0 < j * I := Nat.mul_pos hj hI
  omega

/-- **The states are derivable as far as the chain verdicts are settled**: once every scanned
round of the intervals up to `n` has a chain verdict in a view, the view derives a state for
every interval up to `n + 1`, SH10c at each step. -/
theorem exists_periodAt_of_settled {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {upd : UpdateRule BlockId}
    {k₀ : ℕ} {V : View Validator BlockId Payload U} {n : ℕ}
    (hall : ∀ r, 1 ≤ r → intervalOf I r ≤ n → ∃ v, ChainDecided wa coin U V r v) :
    ∀ j, j ≤ n + 1 → ∃ st, PeriodAt I wa coin upd k₀ U V w j st := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨_, PeriodAt.zero⟩
  | succ j ih =>
    intro hj
    obtain ⟨st, hst⟩ := ih (by omega)
    exact exists_periodAt_succ hw hst fun r hpos hr => hall r hpos (by omega)

omit S in
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

/-- **SH10g.** Induction on the derivation: the initial period is in range, the failover's `1` is,
and the update rule keeps the range. -/
theorem periodAt_mem_range {K : ℕ} {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) {j : ℕ} {st : ScanState}
    (hp : PeriodAt I wa coin upd k₀ U V w j st) : 1 ≤ st.period ∧ st.period ≤ K := by
  induction hp with
  | zero => exact ⟨h₀, hK⟩
  | anchor _ _ _ ih =>
    dsimp only
    split_ifs
    · exact ⟨le_rfl, le_trans h₀ hK⟩
    · exact hupd _ _ ih.1 ih.2
  | keep _ _ ih => exact ih

/-! ## SH10i, SH10j -/

/-- **SH10i.** Induction on the derivation: a slot consumed at an anchor is decided in the
anchor's history, which lies inside the view, and verdicts are monotone in the view. -/
theorem decided_of_lt_next {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j : ℕ} {st : ScanState}
    (hp : PeriodAt I wa coin upd k₀ U V w j st) :
    ∀ s, 1 ≤ s → s < st.next → ∃ v, Decided w U V s v := by
  induction hp with
  | zero =>
    intro s h₁ h₂
    dsimp only at h₂
    omega
  | @anchor j r next' last' st A hA hp ha hadv ih =>
    intro s h₁ h₂
    dsimp only at h₂
    by_cases hlt : s < st.next
    · exact ih s h₁ hlt
    · obtain ⟨v, hv⟩ := hadv.decided s (not_lt.mp hlt) h₂
      exact ⟨v, AnchoredRule.decided_mono (S := S)
        (steelheadLaws (Validator := Validator) (BlockId := BlockId) (Payload := Payload) hw)
        trivial (historyView_ids_subset hA ha.mem_ids) hv⟩
  | keep _ _ ih => exact ih

/-- **An undecided slot stops the advance**: the cursor cannot pass it, since a consumed slot is
decided in the view, and the last commit is the old one or a consumed slot's round, below it. -/
theorem AgreedAdvance.le_of_stalled {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r)
    (hid : ∀ t, S.slotRound t = t) {V : View Validator BlockId Payload U} {A : BlockId}
    {hA : A ∈ U.ids} (hAV : A ∈ V.ids) {s : ℕ} (hund : ∀ v, ¬ Decided w U V s v)
    {next next' last last' : ℕ} (hnext : next ≤ s) (hlast : last ≤ s)
    (h : AgreedAdvance U w A hA next next' last last') : next' ≤ s ∧ last' ≤ s := by
  have hmono : ∀ {t : ℕ} {v : Option BlockId}, Decided w U (U.historyView A hA) t v →
      Decided w U V t v :=
    fun hd => AnchoredRule.decided_mono (S := S)
      (steelheadLaws (Validator := Validator) (BlockId := BlockId) (Payload := Payload) hw)
      trivial (historyView_ids_subset hA hAV) hd
  have hn : next' ≤ s := by
    by_contra hlt
    obtain ⟨v, hv⟩ := h.decided s hnext (not_le.mp hlt)
    exact hund v (hmono hv)
  refine ⟨hn, ?_⟩
  rcases h.last_mem with heq | ⟨t, L, _, ht₂, _, ht⟩
  · rw [heq]; exact hlast
  · rw [← ht, hid]; omega

/-- **SH10j.** Induction on the derivation, the advance stopped at every anchor. -/
theorem stalled_below_undecided {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r)
    (hid : ∀ t, S.slotRound t = t) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j s : ℕ} {st : ScanState}
    (hp : PeriodAt I wa coin upd k₀ U V w j st) (h₁ : 1 ≤ s)
    (hund : ∀ v, ¬ Decided w U V s v) : st.next ≤ s ∧ st.lastCommit ≤ s := by
  induction hp with
  | zero => exact ⟨h₁, Nat.zero_le _⟩
  | @anchor j r next' last' st A hA hp ha hadv ih =>
    exact hadv.le_of_stalled hw hid ha.mem_ids hund ih.1 ih.2
  | keep _ _ ih => exact ih

omit S in
/-- **SH10k.** The rounds from `top − I` to `top − wa + 1` number at least `k`, so one of them is a
multiple of `k`. -/
theorem window_resolves {K k top : ℕ} (hk : 1 ≤ k) (hK : k ≤ K) (hwa : 1 ≤ wa)
    (hI : K + wa - 2 ≤ I) (htop : I ≤ top) :
    ∃ r, top - I ≤ r ∧ r + wa - 1 ≤ top ∧ IsAsync k r := by
  obtain ⟨q, m, hm, hqm⟩ : ∃ q m, m < k ∧ k * q + m = top - I + k - 1 :=
    ⟨(top - I + k - 1) / k, (top - I + k - 1) % k, Nat.mod_lt _ (by omega), Nat.div_add_mod _ _⟩
  exact ⟨k * q, by omega, by omega, Nat.mul_mod_right k q⟩

/-! ## SH14 -/

/-- The derivation of an interval's state ends in an anchor step or a keep step. -/
theorem PeriodAt.succ_cases {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j : ℕ} {st' : ScanState}
    (h : PeriodAt I wa coin upd k₀ U V w (j + 1) st') :
    (∃ (st : ScanState) (r : ℕ) (A : BlockId) (next' last' : ℕ) (hA : A ∈ U.ids),
        PeriodAt I wa coin upd k₀ U V w j st ∧ IntervalAnchor I wa coin U V j r A ∧
        AgreedAdvance U w A hA st.next next' st.lastCommit last' ∧
        st' = ⟨if last' + I < r then 1 else upd A st.period, next', last'⟩) ∨
      ∃ st, PeriodAt I wa coin upd k₀ U V w j st ∧ NoAnchor I wa coin U V j ∧ st' = st := by
  cases h with
  | anchor hp hA hadv => exact Or.inl ⟨_, _, _, _, _, _, hp, hA, hadv, rfl⟩
  | keep hp hn => exact Or.inr ⟨_, hp, hn, rfl⟩

omit S in
/-- A round past `(j + 1) · I` lies in an interval past `j`. -/
theorem le_intervalOf_of_lt {j b : ℕ} (hI : 0 < I) (h : (j + 1) * I < b) :
    j + 1 ≤ intervalOf I b := by
  unfold intervalOf
  rw [Nat.le_div_iff_mul_le hI]
  omega

omit S in
/-- An anchor of an interval two or more past a slot's lies more than `I` rounds above the slot. -/
theorem lt_of_anchor_far {V : View Validator BlockId Payload U} (hI : 0 < I) {s j r : ℕ}
    {A : BlockId} (hj : intervalOf I s + 1 < j) (hA : IntervalAnchor I wa coin U V j r A) :
    s + I < r := by
  have hsI := le_of_intervalOf hI (rfl : intervalOf I s = intervalOf I s)
  have hr : j * I + 1 ≤ r := mul_add_one_le_of_intervalOf hI (by omega) hA.mem
  have h2 : (intervalOf I s + 1) * I ≤ (j - 1) * I := Nat.mul_le_mul_right I (by omega)
  have h3 : j * I = (j - 1) * I + I := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  omega

variable {ws : ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ} {V : View Validator BlockId Payload U}
  {per : ℕ → ℕ}

/-- The adaptive wavelength is at least two rounds everywhere when both waves are: what the laws
need to carry a verdict between views. -/
theorem adaptiveWave_two_le (hws : 2 ≤ ws) (hwa : 2 ≤ wa) (r : ℕ) :
    2 ≤ adaptiveWave ws wa I per r := by
  unfold adaptiveWave periodic
  split <;> omega

/-- **The failover fires at every anchor more than `I` rounds above an undecided slot**: the state
the interval was derived under is stalled below the slot (SH10j), the advance stays there, so the
last commit lies below the slot and the test holds. -/
theorem period_eq_one_of_anchor_far (hws : 2 ≤ ws) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hI : 0 < I) {s j : ℕ} (h₁ : 1 ≤ s)
    (hund : ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s v) (hj : intervalOf I s + 1 < j)
    {st' : ScanState} (hp' : PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) (j + 1) st')
    {r : ℕ} {A : BlockId} (hA : IntervalAnchor I wa coin U V j r A) : st'.period = 1 := by
  have hw2 : ∀ r, 2 ≤ adaptiveWave ws wa I per r := adaptiveWave_two_le hws (by omega)
  rcases hp'.succ_cases with ⟨st, r', A', next', last', hA', hp, hA'', hadv, rfl⟩ |
    ⟨st, hp, hn, rfl⟩
  · dsimp only
    have hst := stalled_below_undecided hw2 hid hp h₁ hund
    have hle := hadv.le_of_stalled hw2 hid hA''.mem_ids hund hst.1 hst.2
    have hfar := lt_of_anchor_far hI hj hA''
    rw [if_pos (by omega)]
  · exact (hA.not_noAnchor hwa hn).elim

/-- **SH14.** If the slot is undecided, every anchor two or more intervals up lies more than `I`
rounds above it while the agreed output waits below it, so the failover fires at the anchored
interval and at every anchored interval after it, and the period is `1` from the next interval on,
up to the run; the run's rounds then carry wave `wa`, its coins commit their candidates directly,
and the drain (SH9) decides every slot below the run, the slot among them. -/
theorem output_liveness (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hI : 0 < I) {b : ℕ}
    (hper : ∀ j, j ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) j st ∧ per j = st.period)
    (hlead : ∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r)
    {s j₁ r₁ : ℕ} {A : BlockId} (h₁ : 1 ≤ s) (hs : intervalOf I s + 1 < j₁)
    (hA : IntervalAnchor I wa coin U V j₁ r₁ A) (hb : (j₁ + 1) * I < b)
    (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v := by
  classical
  by_cases hdec : ∃ v, Decided (adaptiveWave ws wa I per) U V s v
  · exact hdec
  replace hdec : ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s v := fun v hv => hdec ⟨v, hv⟩
  -- the run lies in intervals past the anchored one, all of them derived
  have hbj : j₁ + 1 ≤ intervalOf I b := le_intervalOf_of_lt hI hb
  have hbN : intervalOf I b ≤ intervalOf I (b + wa - 1) := intervalOf_mono (by omega)
  -- the period is 1 from the interval after the anchored one up to the run's
  have hone : ∀ n, j₁ + 1 + n ≤ intervalOf I (b + wa - 1) → per (j₁ + 1 + n) = 1 := by
    intro n
    induction n with
    | zero =>
      intro hn
      obtain ⟨st', hp', he'⟩ := hper (j₁ + 1) hn
      change per (j₁ + 1) = 1
      rw [he']
      exact period_eq_one_of_anchor_far hws hwa hid hI h₁ hdec hs hp' hA
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      obtain ⟨st', hp', he'⟩ := hper (j₁ + 1 + n + 1) hn
      change per (j₁ + 1 + n + 1) = 1
      rw [he']
      rcases hp'.succ_cases with ⟨st, r, A', next', last', hA', hp, hA'', hadv, rfl⟩ |
        ⟨st, hp, _, rfl⟩
      · exact period_eq_one_of_anchor_far hws hwa hid hI h₁ hdec (by omega) hp' hA''
      · obtain ⟨st'', hp'', he''⟩ := hper (j₁ + 1 + n) (by omega)
        rw [← hprev, he'']
        exact congrArg ScanState.period (periodAt_unique hwa hp hp'')
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
    have hsI := le_of_intervalOf hI (rfl : intervalOf I s = intervalOf I s)
    have h2 : (intervalOf I s + 1) * I ≤ j₁ * I := Nat.mul_le_mul_right I (by omega)
    have h3 : j₁ * I ≤ (j₁ + 1) * I := Nat.mul_le_mul_right I (by omega)
    omega
  exact allDecidedBelowOfRun
    (fun r => Nat.le_of_succ_le (adaptiveWave_two_le (I := I) (per := per) hws (by omega) r))
    (fun r => by unfold adaptiveWave periodic; split <;> omega) hid hrun s hsb

/-! ## SH14b -/

omit S in
/-- A round strictly above `j · I` and at most `(j + 1) · I` lies in interval `j`. -/
theorem intervalOf_eq_of_mul_lt_le {j r : ℕ} (h₁ : j * I < r) (h₂ : r ≤ (j + 1) * I) :
    intervalOf I r = j := by
  unfold intervalOf
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

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
/-- **A good coin gives its round a chain commit** in a view holding the decision round. -/
theorem chainCommit_of_good {V : View Validator BlockId Payload U} {r N : ℕ}
    (hg : coin r ∈ MahiMahi.goodAt U wa r) (hV : V.CoversUpto N)
    (hN : MahiMahi.decisionRoundAt wa r ≤ N) :
    ∃ L, ChainDecided wa coin U V r (some L) := by
  obtain ⟨L, hLU, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hg
  exact ⟨L, MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hLU, hLr, hLc⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono hN))⟩

/-- **SH14b.** The run of `K` inside the second interval after the slot's chain-commits its first
round, which gives the interval its anchor once SH7a has settled every chain verdict there; the
run in the next interval is the one SH14 needs. -/
theorem all_decided (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa) (hid : ∀ t, S.slotRound t = t)
    (hI : 0 < I) (hlead : ∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r)
    {K c N : ℕ} (hwaK : wa ≤ K) (hcK : c + K ≤ I)
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c K N)
    (hV : V.CoversUpto N)
    (hper : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) j st ∧ per j = st.period)
    (s : ℕ) (h₁ : 1 ≤ s)
    (hN : MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + c + K) ≤ N) :
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v := by
  have hmul2 : (intervalOf I s + 2) * I = intervalOf I s * I + I + I := by
    rw [Nat.add_mul, Nat.two_mul, ← Nat.add_assoc]
  have hmul3 : (intervalOf I s + 3) * I = intervalOf I s * I + I + I + I := by
    rw [Nat.add_mul, show (3 : ℕ) * I = I + I + I by omega, ← Nat.add_assoc, ← Nat.add_assoc]
  have hmul4 : (intervalOf I s + 2 + 1) * I = (intervalOf I s + 3) * I := rfl
  have hmul5 : (intervalOf I s + 1 + 1) * I = (intervalOf I s + 2) * I := rfl
  unfold MahiMahi.decisionRoundAt at hN
  -- every chain verdict of the second interval after the slot's is settled
  have hall := chain_all_of_clause (by omega) hI
    (unpredictableRunWithin_of_le (by omega) hwaK (by omega) hrun)
    (hV.mono (Nat.sub_le _ _)) (j := intervalOf I s + 2) (by
      unfold MahiMahi.decisionRoundAt
      omega)
  -- a run of K good coins inside that interval chain-commits its first round
  obtain ⟨k', hk1, hk2, hg⟩ := hrun ((intervalOf I s + 2) * I + 1) (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) (by omega)]
    change MahiMahi.decisionRoundAt wa ((intervalOf I s + 2) * I + 1 + c + K - 1) ≤ N
    unfold MahiMahi.decisionRoundAt
    omega)
  have hmem : intervalOf I k' = intervalOf I s + 2 :=
    intervalOf_eq_of_mul_lt_le (by omega) (by omega)
  have hg0 : coin k' ∈ MahiMahi.goodAt U wa k' := hg 0 (by omega)
  have hk'N : MahiMahi.decisionRoundAt wa k' ≤ N := by
    unfold MahiMahi.decisionRoundAt
    omega
  obtain ⟨L, hL⟩ := chainCommit_of_good (V := V) hg0 hV hk'N
  obtain ⟨r₁, A, hA⟩ :=
    IntervalAnchor.of_committed (fun r _ hr => hall r hr) ⟨k', by omega, hmem, L, hL⟩
  -- the run of K in the next interval starts the run of wa SH14 needs
  obtain ⟨b, hb1, hb2, hgb⟩ := hrun ((intervalOf I s + 3) * I + 1) (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) (by omega)]
    change MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + 1 + c + K - 1) ≤ N
    unfold MahiMahi.decisionRoundAt
    omega)
  refine output_liveness hws hle hwa hid hI (b := b) (fun j hj => hper j ?_) hlead h₁
    (by omega) hA (by omega) (fun i hi => hgb i (by omega)) (hV.mono (by
      unfold MahiMahi.decisionRoundAt
      omega))
  exact le_trans hj (intervalOf_mono (by omega))

/-! ## SH14c -/

/-- **SH14c.** The good coin opening interval `j` chain-commits its first round; the `wa` good
coins above the interval settle every chain verdict below them (SH7c), so interval `j` has its
anchor, and they are the run SH14 needs. -/
theorem output_liveness_of_runs (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hI : 0 < I)
    (hlead : ∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) {b : ℕ}
    (hper : ∀ j', j' ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) j' st ∧ per j' = st.period)
    {s j : ℕ} (h₁ : 1 ≤ s) (hs : intervalOf I s + 1 < j)
    (hgood : coin (j * I + 1) ∈ MahiMahi.goodAt U wa (j * I + 1))
    (hb : (j + 1) * I < b) (hgoodb : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v := by
  have hmul : (j + 1) * I = j * I + I := by rw [Nat.add_mul, Nat.one_mul]
  -- the run above settles every chain verdict of interval j
  have hall := chainAllDecidedBelowOfRun (by omega) hgoodb hV
  have hmem : intervalOf I (j * I + 1) = j := intervalOf_eq_of_mul_lt_le (by omega) (by omega)
  -- the coin opening the interval chain-commits its round
  obtain ⟨L, hL⟩ := chainCommit_of_good (V := V) hgood hV (by
    unfold MahiMahi.decisionRoundAt
    omega)
  obtain ⟨r₁, A, hA⟩ := IntervalAnchor.of_committed
    (fun r _ hr => hall r (by have := le_of_intervalOf hI hr; omega))
    ⟨j * I + 1, by omega, hmem, L, hL⟩
  exact output_liveness hws hle hwa hid hI hper hlead h₁ hs hA hb hgoodb hV

end Slots

end Steelhead

end LeanDag
