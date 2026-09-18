import LeanDag.Steelhead.Period.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Helpers — the period layer

Generated lemma infrastructure for `Period/Statement.lean`; not part of
the audit surface. The control schedule's rounds strictly increase and
enumerate the control rounds; control agreement (SH10m) makes the anchor
of an interval unique across views and excludes an anchor in one view
against none in another; the agreed output's advance over an anchor's
history is unique and exists, since no verdict of a history lies above
the anchor's round; the period sequence follows by induction on its
derivation; the scan ends by taking the least committed control slot;
under the clause SH7a at the scan's own schedule settles every control
slot of an interval.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload} {I K wa : ℕ} [NeZero K]
  {coin : ℕ → Validator}

/-! ## The control schedule -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The period bound is positive. -/
theorem pos_of_neZero : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)

omit [Fintype Validator] [DecidableEq Validator] F [NeZero K] in
/-- Up to the boundary index a control slot's round is its index times the period. -/
theorem controlRound_of_le {j k i : ℕ} (h : i ≤ (j + 1) * I / k) :
    controlRound I K j k i = i * k := if_pos h

omit [Fintype Validator] [DecidableEq Validator] F [NeZero K] in
/-- Above the boundary index a control slot's round is a multiple of the bound. -/
theorem controlRound_of_gt {j k i : ℕ} (h : (j + 1) * I / k < i) :
    controlRound I K j k i = ((j + 1) * I / K + (i - (j + 1) * I / k)) * K :=
  if_neg (not_le.mpr h)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Above the boundary index a control slot lies above the boundary. -/
theorem lt_controlRound_of_gt {j k i : ℕ} (h : (j + 1) * I / k < i) :
    (j + 1) * I < controlRound I K j k i := by
  rw [controlRound_of_gt h]
  calc (j + 1) * I < (j + 1) * I / K * K + K := Nat.lt_div_mul_add pos_of_neZero
    _ = ((j + 1) * I / K + 1) * K := (Nat.succ_mul _ _).symm
    _ ≤ ((j + 1) * I / K + (i - (j + 1) * I / k)) * K := Nat.mul_le_mul_right K (by omega)

omit [Fintype Validator] [DecidableEq Validator] F [NeZero K] in
/-- Above the boundary index a control slot lies at most its excess times the bound above it. -/
theorem controlRound_le_of_gt {j k i : ℕ} (h : (j + 1) * I / k < i) :
    controlRound I K j k i ≤ (j + 1) * I + (i - (j + 1) * I / k) * K := by
  rw [controlRound_of_gt h, Nat.add_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A control slot lies at or below the boundary exactly when its index does. -/
theorem controlRound_le_boundary_iff {j k i : ℕ} :
    controlRound I K j k i ≤ (j + 1) * I ↔ i ≤ (j + 1) * I / k := by
  constructor
  · intro h
    by_contra hi
    exact absurd h (not_le.mpr (lt_controlRound_of_gt (not_le.mp hi)))
  · intro h
    rw [controlRound_of_le h]
    exact le_trans (Nat.mul_le_mul_right k h) (Nat.div_mul_le_self _ _)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The control rounds strictly increase with the slot index. -/
theorem controlRound_strictMono (j k : ℕ) : StrictMono (controlRound I K j k) := by
  intro i i' h
  have hK : 0 < K := pos_of_neZero
  unfold controlRound
  split_ifs with hi hi'
  · have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp at hi'; omega
      · exact hk
    exact Nat.mul_lt_mul_of_pos_right h hk
  · calc i * k ≤ (j + 1) * I / k * k := Nat.mul_le_mul_right k hi
      _ ≤ (j + 1) * I := Nat.div_mul_le_self _ _
      _ < (j + 1) * I / K * K + K := Nat.lt_div_mul_add hK
      _ = ((j + 1) * I / K + 1) * K := (Nat.succ_mul _ _).symm
      _ ≤ ((j + 1) * I / K + (i' - (j + 1) * I / k)) * K :=
          Nat.mul_le_mul_right K (by omega)
  · omega
  · exact Nat.mul_lt_mul_of_pos_right (by omega) hK

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The control schedule's rounds are `controlRound`. -/
@[simp] theorem controlSlots_slotRound (j k i : ℕ) :
    (controlSlots coin I K j k).slotRound i = controlRound I K j k i := rfl

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The control schedule's leader is the coin of the slot's round. -/
@[simp] theorem controlSlots_leader (j k i : ℕ) :
    (controlSlots coin I K j k).leader i = coin (controlRound I K j k i) := rfl

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Every control slot is of the asynchronous kind. -/
@[simp] theorem controlSlots_kind (j k i : ℕ) : (controlSlots coin I K j k).kind i = 1 := rfl

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **SH10l.** Up to the boundary the multiples of the period are the slots `i · k`, above it the
multiples of the bound are the slots past the boundary index. -/
theorem controlRounds (j k r : ℕ) :
    (∃ i, controlRound I K j k i = r) ↔
      (r ≤ (j + 1) * I ∧ r % k = 0) ∨ ((j + 1) * I < r ∧ r % K = 0) := by
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i ≤ (j + 1) * I / k
    · exact Or.inl ⟨controlRound_le_boundary_iff.mpr hi,
        by rw [controlRound_of_le hi]; exact Nat.mul_mod_left i k⟩
    · exact Or.inr ⟨lt_controlRound_of_gt (not_le.mp hi),
        by rw [controlRound_of_gt (not_le.mp hi)]; exact Nat.mul_mod_left _ K⟩
  · rintro (⟨hr, hk⟩ | ⟨hr, hK⟩)
    · refine ⟨r / k, ?_⟩
      have hle : r / k ≤ (j + 1) * I / k := Nat.div_le_div_right hr
      rw [controlRound_of_le hle]
      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hk)
    · have hKpos : 0 < K := pos_of_neZero
      have hdiv : (j + 1) * I / K < r / K := by
        rw [Nat.div_lt_iff_lt_mul hKpos, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hK)]
        exact hr
      refine ⟨(j + 1) * I / k + (r / K - (j + 1) * I / K), ?_⟩
      rw [controlRound_of_gt (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel' hdiv.le]
      exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hK)

/-! ## Control agreement, per scan -/

/-- **SH10m.** Two views agree on a control verdict of one scan: MM1c at the control schedule. -/
theorem controlDecided_unique (hwa : 3 ≤ wa) {j k : ℕ} {V₁ V₂ : View Validator BlockId Payload U}
    {i : ℕ} {v₁ v₂ : Option BlockId} (h₁ : ControlDecided I K wa coin j k U V₁ i v₁)
    (h₂ : ControlDecided I K wa coin j k U V₂ i v₂) : v₁ = v₂ :=
  AnchoredRule.decided_unique (S := controlSlots coin I K j k) (MahiMahi.mahiMahiLaws (by omega))
    trivial h₁ V₂ v₂ h₂

/-- An anchor in one view is never a skipped control slot in another. -/
theorem IntervalAnchor.not_none (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j k i : ℕ} {A : BlockId} (h : IntervalAnchor I K wa coin U V₁ j k i A)
    (hn : ControlDecided I K wa coin j k U V₂ i none) : False :=
  Option.some_ne_none A (controlDecided_unique hwa h.commit hn)

/-- **The anchor is unique across views.** -/
theorem IntervalAnchor.unique (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j k i₁ i₂ : ℕ} {A₁ A₂ : BlockId} (h₁ : IntervalAnchor I K wa coin U V₁ j k i₁ A₁)
    (h₂ : IntervalAnchor I K wa coin U V₂ j k i₂ A₂) : i₁ = i₂ ∧ A₁ = A₂ := by
  rcases lt_trichotomy i₁ i₂ with h | h | h
  · exact absurd (h₂.below i₁ h₁.pos h₁.mem h) (fun hn => h₁.not_none hwa hn)
  · subst h
    exact ⟨rfl, Option.some.inj (controlDecided_unique hwa h₁.commit h₂.commit)⟩
  · exact absurd (h₁.below i₂ h₂.pos h₂.mem h) (fun hn => h₂.not_none hwa hn)

/-- An anchor in one view excludes no anchor in another. -/
theorem IntervalAnchor.not_noAnchor (hwa : 3 ≤ wa) {V₁ V₂ : View Validator BlockId Payload U}
    {j k i : ℕ} {A : BlockId} (h : IntervalAnchor I K wa coin U V₁ j k i A)
    (hn : NoAnchor I K wa coin U V₂ j k) : False :=
  h.not_none hwa (hn i h.pos h.mem)

/-- The anchor's block lies in the record. -/
theorem IntervalAnchor.mem_ids_U {V : View Validator BlockId Payload U} {j k i : ℕ}
    {A : BlockId} (h : IntervalAnchor I K wa coin U V j k i A) : A ∈ U.ids :=
  (AnchoredRule.isLeaderBlock_of_decided (S := controlSlots coin I K j k) h.commit).1

/-- The anchor's block sits at the anchor's round. -/
theorem IntervalAnchor.round_eq {V : View Validator BlockId Payload U} {j k i : ℕ} {A : BlockId}
    (h : IntervalAnchor I K wa coin U V j k i A) : (U.block A).round = controlRound I K j k i :=
  (AnchoredRule.isLeaderBlock_of_decided (S := controlSlots coin I K j k) h.commit).2.1

/-! ## The anchor's history, inside the view that found it

The agreed output is read in the anchor's causal history; the validator holds a view. The two
agree on what the output asks because the history lies inside the view: a committed block is in
the view that committed it, since a certificate the view holds references a vote referencing the
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
theorem IntervalAnchor.mem_ids {V : View Validator BlockId Payload U} {j k i : ℕ} {A : BlockId}
    (h : IntervalAnchor I K wa coin U V j k i A) : A ∈ V.ids :=
  mem_ids_of_mahiMahi_decided h.commit A rfl

/-- The causal history of a block a view holds lies inside the view. -/
theorem historyView_ids_subset {V : View Validator BlockId Payload U} {A : BlockId} (hA : A ∈ U.ids)
    (hAV : A ∈ V.ids) : (U.historyView A hA).ids ⊆ V.ids :=
  fun _ hi => mem_of_reaches_of_closed V.complete hAV ((mem_history_iff hA).mp hi)

section Slots

variable [S : Slots Validator]

/-- **A verdict reads the wavelength only at the kinds of the slots its derivation names.**
Those are the slot itself and, above it, the anchor the derivation rests on and the eligible
slots it skipped on the way, every one of them proposed at or below the round of a block the
anchor's candidate is. The hypothesis below is coarser than that: agreement at the kind of every
slot proposed at or below a bound `N` on the rounds of the view's blocks, under which a slot
proposed at or below `N` decides alike. -/
theorem decided_congr {w₁ w₂ : ℕ → ℕ} {N : ℕ} {V : View Validator BlockId Payload U}
    (hN : ∀ b ∈ V.ids, (U.block b).round ≤ N)
    (hw : ∀ k, S.slotRound k ≤ N → w₁ (S.kind k) = w₂ (S.kind k)) {k : ℕ}
    {v : Option BlockId} (h : Decided w₁ U V k v) :
    S.slotRound k ≤ N → Decided w₂ U V k v := by
  -- the anchor of an indirect step is a block the view committed, so its round is under the
  -- bound too
  have hanchor : ∀ {j : ℕ} {A : BlockId}, Decided w₁ U V j (some A) → S.slotRound j ≤ N := by
    intro j A hj
    have := hN A (mem_ids_of_decided hj A rfl)
    rw [(AnchoredRule.isLeaderBlock_of_decided hj).2.1] at this
    exact this
  -- eligibility reads the wave at the slot's own kind, which the bound covers
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
    change MahiMahi.DirectCommitIn U V (w₂ (S.kind k)) L (S.slotRound k)
    rw [← hw _ hk]; exact hc
  | @directSkip k hs =>
    intro hk
    refine Decided.directSkip ?_
    change MahiMahi.DirectSkipIn U V (w₂ (S.kind k)) (S.leader k) (S.slotRound k)
    rw [← hw _ hk]; exact hs
  | @indirectCommit k j A L i hkj he hj hmid hi hemp hL hlink _ ihj ihmid =>
    intro hk
    have hjN := hanchor hj
    refine Decided.indirectCommit hkj ((helig hk).mpr he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)
        (le_trans (S.mono h2.le) hjN)) hi (fun i' hi' L' hL' hl => ?_) hL ?_ (fun _ _ _ h => h)
    · refine hemp i' hi' L' hL' ?_
      change MahiMahi.CertifiedIn U (w₁ (S.kind k)) A L' (S.slotRound k)
      rw [hw _ hk]; exact hl
    · change MahiMahi.CertifiedIn U (w₂ (S.kind k)) A L (S.slotRound k)
      rw [← hw _ hk]; exact hlink
  | @indirectSkip k j A hkj he hj hmid hnone ihj ihmid =>
    intro hk
    have hjN := hanchor hj
    refine Decided.indirectSkip hkj ((helig hk).mpr he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)
        (le_trans (S.mono h2.le) hjN)) (fun i hi L' hL' hl => ?_)
    refine hnone i hi L' hL' ?_
    change MahiMahi.CertifiedIn U (w₁ (S.kind k)) A L' (S.slotRound k)
    rw [hw _ hk]; exact hl

/-- **A verdict reads the wavelength only at the slots the view decides**: its own, the anchor's
and the skipped slots between, each of them decided in the view. Two wavelength functions that
agree at the kind of every slot the view decides under the first give the same verdicts. -/
theorem decided_congr_of_decided {w₁ w₂ : ℕ → ℕ} {V : View Validator BlockId Payload U}
    (hw : ∀ (r : ℕ) (v : Option BlockId), Decided w₁ U V r v → w₁ (S.kind r) = w₂ (S.kind r))
    {k : ℕ} {v : Option BlockId} (h : Decided w₁ U V k v) : Decided w₂ U V k v := by
  have helig : ∀ {k m : ℕ}, w₁ (S.kind k) = w₂ (S.kind k) →
      ((steelheadAnchored Validator BlockId Payload w₂).Eligible k m ↔
        (steelheadAnchored Validator BlockId Payload w₁).Eligible k m) := by
    intro k m hk
    rw [AnchoredRule.eligible_iff, AnchoredRule.eligible_iff]
    simp only [steelheadAnchored_waveAt, hk]
  induction h with
  | @directCommit k L hL hc =>
    have hk := hw k _ (Decided.directCommit hL hc)
    refine Decided.directCommit hL ?_
    change MahiMahi.DirectCommitIn U V (w₂ (S.kind k)) L (S.slotRound k)
    rw [← hk]; exact hc
  | @directSkip k hs =>
    have hk := hw k _ (Decided.directSkip hs)
    refine Decided.directSkip ?_
    change MahiMahi.DirectSkipIn U V (w₂ (S.kind k)) (S.leader k) (S.slotRound k)
    rw [← hk]; exact hs
  | @indirectCommit k j A L i hkj he hj hmid hi hemp hL hlink hleast ihj ihmid =>
    have hk := hw k _ (Decided.indirectCommit hkj he hj hmid hi hemp hL hlink hleast)
    refine Decided.indirectCommit hkj ((helig hk).mpr he) ihj
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)) hi
      (fun i' hi' L' hL' hl => ?_) hL ?_ (fun _ _ _ h => h)
    · refine hemp i' hi' L' hL' ?_
      change MahiMahi.CertifiedIn U (w₁ (S.kind k)) A L' (S.slotRound k)
      rw [hk]; exact hl
    · change MahiMahi.CertifiedIn U (w₂ (S.kind k)) A L (S.slotRound k)
      rw [← hk]; exact hlink
  | @indirectSkip k j A hkj he hj hmid hnone ihj ihmid =>
    have hk := hw k _ (Decided.indirectSkip hkj he hj hmid hnone)
    refine Decided.indirectSkip hkj ((helig hk).mpr he) ihj
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mp h3)) (fun i hi L' hL' hl => ?_)
    refine hnone i hi L' hL' ?_
    change MahiMahi.CertifiedIn U (w₁ (S.kind k)) A L' (S.slotRound k)
    rw [hk]; exact hl

omit S in
/-- **A verdict reads the schedule only at the slots its derivation names**: the slot's own and,
above it, the anchor's and the eligible slots skipped on the way, each proposed at or below the
round of a block the view holds. Two schedules that agree on the round of every slot and on the
leader and the kind of every slot proposed at or below a bound `N` on the view's blocks give the
same verdict at a slot proposed at or below `N`. -/
theorem decided_congr_slots {S₁ S₂ : Slots Validator} {w : ℕ → ℕ} {N : ℕ}
    {V : View Validator BlockId Payload U} (hN : ∀ b ∈ V.ids, (U.block b).round ≤ N)
    (hround : ∀ t, S₁.slotRound t = S₂.slotRound t)
    (hlead : ∀ t, S₁.slotRound t ≤ N → S₁.leader t = S₂.leader t)
    (hkind : ∀ t, S₁.slotRound t ≤ N → S₁.kind t = S₂.kind t) {k : ℕ} {v : Option BlockId}
    (h : Decided (S := S₁) w U V k v) : S₁.slotRound k ≤ N → Decided (S := S₂) w U V k v := by
  -- the anchor of an indirect step is a block the view committed, so its round is under the
  -- bound too
  have hanchor : ∀ {j : ℕ} {A : BlockId}, Decided (S := S₁) w U V j (some A) →
      S₁.slotRound j ≤ N := by
    intro j A hj
    have := hN A (mem_ids_of_decided (S := S₁) hj A rfl)
    rw [(AnchoredRule.isLeaderBlock_of_decided (S := S₁) hj).2.1] at this
    exact this
  have hleader : ∀ {k : ℕ} {L : BlockId}, S₁.slotRound k ≤ N →
      (IsLeaderBlock (S := S₁) U k L ↔ IsLeaderBlock (S := S₂) U k L) := by
    intro k L hk
    change (L ∈ U.ids ∧ (U.block L).round = S₁.slotRound k ∧ (U.block L).creator = S₁.leader k) ↔
      (L ∈ U.ids ∧ (U.block L).round = S₂.slotRound k ∧ (U.block L).creator = S₂.leader k)
    rw [hround k, hlead k hk]
  have helig : ∀ {k m : ℕ}, S₁.slotRound k ≤ N →
      ((steelheadAnchored Validator BlockId Payload w).Eligible (S := S₁) k m ↔
        (steelheadAnchored Validator BlockId Payload w).Eligible (S := S₂) k m) := by
    intro k m hk
    rw [AnchoredRule.eligible_iff (S := S₁), AnchoredRule.eligible_iff (S := S₂), hkind k hk,
      hround k, hround m]
  induction h with
  | @directCommit k L hL hc =>
    intro hk
    refine Decided.directCommit (S := S₂) ((hleader hk).mp hL) ?_
    rw [← hround k, ← hkind k hk]; exact hc
  | @directSkip k hs =>
    intro hk
    refine Decided.directSkip (S := S₂) ?_
    change MahiMahi.DirectSkipIn U V (w (S₂.kind k)) (S₂.leader k) (S₂.slotRound k)
    rw [← hround k, ← hlead k hk, ← hkind k hk]; exact hs
  | @indirectCommit k j A L i hkj he hj hmid hi hemp hL hlink _ ihj ihmid =>
    intro hk
    have hjN := hanchor hj
    refine Decided.indirectCommit (S := S₂) hkj ((helig hk).mp he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mpr h3) (le_trans (S₁.mono h2.le) hjN)) hi
      (fun i' hi' L' hL' hl => ?_) ((hleader hk).mp hL) ?_ (fun _ _ _ h => h)
    · refine hemp i' hi' L' ((hleader hk).mpr hL') ?_
      change MahiMahi.CertifiedIn U (w (S₁.kind k)) A L' (S₁.slotRound k)
      rw [hround k, hkind k hk]; exact hl
    · change MahiMahi.CertifiedIn U (w (S₂.kind k)) A L (S₂.slotRound k)
      rw [← hround k, ← hkind k hk]; exact hlink
  | @indirectSkip k j A hkj he hj hmid hnone ihj ihmid =>
    intro hk
    have hjN := hanchor hj
    refine Decided.indirectSkip (S := S₂) hkj ((helig hk).mp he) (ihj hjN)
      (fun m h1 h2 h3 => ihmid m h1 h2 ((helig hk).mpr h3) (le_trans (S₁.mono h2.le) hjN))
      (fun i hi L' hL' hl => ?_)
    refine hnone i hi L' ((hleader hk).mpr hL') ?_
    change MahiMahi.CertifiedIn U (w (S₁.kind k)) A L' (S₁.slotRound k)
    rw [hround k, hkind k hk]; exact hl

/-! ## The agreed output over an anchor's history -/

/-- **No verdict of a view lies above the rounds of its blocks**: a direct commit holds a
certificate of the view at the slot's decision round, a direct skip a blame at its vote round,
both at or above the slot's round and at or below the bound; an indirect verdict rests on an
anchor of the view at a higher slot. -/
theorem slotRound_le_of_decided {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ)
    {V : View Validator BlockId Payload U} {N : ℕ} (hN : ∀ b ∈ V.ids, (U.block b).round ≤ N)
    {s : ℕ} {v : Option BlockId} (h : Decided w U V s v) : S.slotRound s ≤ N := by
  induction h with
  | @directCommit k L _ hc =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    have hCr := (mem_certificatesAt.mp hC).2.1
    have hCA := hN C hCV
    have := hw (S.kind k)
    unfold MahiMahi.decisionRoundAt at hCr
    omega
  | @directSkip k hs =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    have hqA := hN q hqV
    have := hw (S.kind k)
    unfold MahiMahi.votingRound at hqr
    omega
  | @indirectCommit k j _ _ _ hkj _ _ _ _ _ _ _ _ ihj _ => exact le_trans (S.mono hkj.le) ihj
  | @indirectSkip k j _ hkj _ _ _ _ ihj _ => exact le_trans (S.mono hkj.le) ihj

/-- **No verdict of an anchor's history lies above the anchor's round**: the history holds no
block above it. -/
theorem slotRound_le_of_decided_historyView {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) {A : BlockId}
    (hA : A ∈ U.ids) {s : ℕ} {v : Option BlockId}
    (h : Decided w U (U.historyView A hA) s v) : S.slotRound s ≤ (U.block A).round :=
  slotRound_le_of_decided hw (fun _ hb => round_le_of_mem_history hA hb) h

/-- **No verdict of an anchor's history has its vote round above the anchor's**: a direct commit
holds a certificate of the history at the slot's decision round, a direct skip a blame at its vote
round, and an indirect verdict rests on an anchor at or above the slot's floor, whose own vote
round is bounded in turn. -/
theorem voteRound_le_of_decided_historyView {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {A : BlockId}
    (hA : A ∈ U.ids) {s : ℕ} {v : Option BlockId}
    (h : Decided w U (U.historyView A hA) s v) :
    S.slotRound s + w (S.kind s) - 2 ≤ (U.block A).round := by
  induction h with
  | @directCommit k L _ hc =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    have hCr := (mem_certificatesAt.mp hC).2.1
    have hCA := round_le_of_mem_history hA hCV
    have := hw (S.kind k)
    unfold MahiMahi.decisionRoundAt at hCr
    omega
  | @directSkip k hs =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    have hqA := round_le_of_mem_history hA hqV
    have := hw (S.kind k)
    unfold MahiMahi.votingRound at hqr
    omega
  | @indirectCommit k j _ _ _ _ he _ _ _ _ _ _ _ ihj _ =>
    rw [AnchoredRule.eligible_iff] at he
    simp only [steelheadAnchored_waveAt] at he
    have := hw (S.kind k)
    have := hw (S.kind j)
    omega
  | @indirectSkip k j _ _ he _ _ _ ihj _ =>
    rw [AnchoredRule.eligible_iff] at he
    simp only [steelheadAnchored_waveAt] at he
    have := hw (S.kind k)
    have := hw (S.kind j)
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

omit S in
/-- **The advance reads the schedule at or below the anchor's round only**: every verdict it
reads is at a slot of the anchor's history, or refuted there, and the history holds no block above
the anchor's round; so two schedules agreeing on every slot's round and on the leaders and kinds
of the slots proposed at or below the anchor's round give one advance. -/
theorem AgreedAdvance.congr_slots {S₁ S₂ : Slots Validator} {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ)
    {A : BlockId} (hA : A ∈ U.ids) (hround : ∀ t, S₁.slotRound t = S₂.slotRound t)
    (hlead : ∀ t, S₁.slotRound t ≤ (U.block A).round → S₁.leader t = S₂.leader t)
    (hkind : ∀ t, S₁.slotRound t ≤ (U.block A).round → S₁.kind t = S₂.kind t)
    {next next' last last' : ℕ} (h : AgreedAdvance (S := S₁) U w A hA next next' last last') :
    AgreedAdvance (S := S₂) U w A hA next next' last last' := by
  have hN : ∀ b ∈ (U.historyView A hA).ids, (U.block b).round ≤ (U.block A).round :=
    fun b hb => round_le_of_mem_history hA hb
  have fwd : ∀ {s : ℕ} {v : Option BlockId},
      Decided (S := S₁) w U (U.historyView A hA) s v →
        Decided (S := S₂) w U (U.historyView A hA) s v :=
    fun hd => decided_congr_slots (S₁ := S₁) (S₂ := S₂) hN hround hlead hkind hd
      (slotRound_le_of_decided_historyView (S := S₁) hw hA hd)
  have bwd : ∀ {s : ℕ} {v : Option BlockId},
      Decided (S := S₂) w U (U.historyView A hA) s v →
        Decided (S := S₁) w U (U.historyView A hA) s v :=
    fun hd => decided_congr_slots (S₁ := S₂) (S₂ := S₁) hN (fun t => (hround t).symm)
      (fun t ht => (hlead t (by rw [hround t]; exact ht)).symm)
      (fun t ht => (hkind t (by rw [hround t]; exact ht)).symm) hd
      (slotRound_le_of_decided_historyView (S := S₂) hw hA hd)
  exact ⟨AgreedAdvance.le (S := S₁) h,
    fun s hs₁ hs₂ => (AgreedAdvance.decided (S := S₁) h s hs₁ hs₂).imp fun _ hv => fwd hv,
    fun v hv => AgreedAdvance.stuck (S := S₁) h v (bwd hv), AgreedAdvance.last_ge (S := S₁) h,
    fun s L hs₁ hs₂ hd => by
      rw [← hround s]; exact AgreedAdvance.last_le (S := S₁) h s L hs₁ hs₂ (bwd hd),
    (AgreedAdvance.last_mem (S := S₁) h).imp id fun ⟨s, L, hs₁, hs₂, hd, hs⟩ =>
      ⟨s, L, hs₁, hs₂, fwd hd, by rw [← hround s]; exact hs⟩⟩

/-! ## SH10a, SH10b -/

/-- **SH10a.** Both views read the agreed output at one wavelength and on one schedule:
induction on the derivation; the periods agree, so the scans read one control schedule, the
anchor is common, the advances over its history agree, so do the failover's test, the warm-up and
the update. -/
theorem periodAt_unique (hwa : 3 ≤ wa) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V₁ V₂ : View Validator BlockId Payload U} {w : ℕ → ℕ} {j : ℕ} {st₁ st₂ : ScanState}
    (h₁ : PeriodAt I K wa coin upd k₀ U V₁ w j st₁)
    (h₂ : PeriodAt I K wa coin upd k₀ U V₂ w j st₂) : st₁ = st₂ := by
  induction h₁ generalizing st₂ with
  | zero => cases h₂; rfl
  | @anchor j i next' last' st A hA hp ha hadv ih =>
    cases h₂ with
    | @anchor _ i₂ next₂ last₂ st₂ A₂ hA₂ hp' ha' hadv' =>
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

/-- Intervals run in round order, so a round below `N` lies in an interval below `N`'s. -/
theorem intervalOf_mono {r N : ℕ} (h : r ≤ N) : intervalOf I r ≤ intervalOf I N :=
  Nat.div_le_div_right (Nat.sub_le_sub_right h 1)

/-- Two period sequences agreeing below `N`'s interval give one kind below `N`. -/
theorem adaptiveKind_congr {per₁ per₂ : ℕ → ℕ} {N : ℕ}
    (h : ∀ j, j ≤ intervalOf I N → per₁ j = per₂ j) {r : ℕ} (hr : r ≤ N) :
    adaptiveKind I per₁ r = adaptiveKind I per₂ r := by
  unfold adaptiveKind
  rw [h _ (intervalOf_mono hr)]

omit S in
/-- **The state of an interval reads the period sequence below that interval only**: the anchor
of interval `j` lies in interval `j`, its history holds verdicts at rounds at or below the
anchor's, and the adaptive schedule's kind and leader at such a round are fixed by the period of
the round's interval, at or below `j`. Two sequences agreeing below an interval give one
derivation of its state, each on its own schedule. -/
theorem periodAt_congr_per {ws : ℕ} (hws : 2 ≤ ws) (hwa : 2 ≤ wa) {known : ℕ → Validator}
    {upd : UpdateRule BlockId} {k₀ : ℕ} {V : View Validator BlockId Payload U}
    {per₁ per₂ : ℕ → ℕ} {j : ℕ} {st : ScanState}
    (hp : PeriodAt (S := adaptiveSlots coin known I per₁) I K wa coin upd k₀ U V
      (wavelength ws wa) j st)
    (h : ∀ i, i < j → per₁ i = per₂ i) :
    PeriodAt (S := adaptiveSlots coin known I per₂) I K wa coin upd k₀ U V
      (wavelength ws wa) j st := by
  induction hp with
  | zero => exact PeriodAt.zero (S := adaptiveSlots coin known I per₂)
  | @anchor j i next' last' st A hA hp ha hadv ih =>
    -- the sequences agree up to the anchor's interval, hence at every round up to its own
    have hagree : ∀ i', i' ≤ intervalOf I (controlRound I K j st.period i) → per₁ i' = per₂ i' := by
      intro i' hi'
      rw [ha.mem] at hi'
      exact h i' (by omega)
    have hkind' : ∀ t, t ≤ (U.block A).round → adaptiveKind I per₁ t = adaptiveKind I per₂ t :=
      fun t ht => adaptiveKind_congr hagree (r := t) (by rw [ha.round_eq] at ht; exact ht)
    have hkind : ∀ t, (adaptiveSlots coin known I per₁).slotRound t ≤ (U.block A).round →
        (adaptiveSlots coin known I per₁).kind t = (adaptiveSlots coin known I per₂).kind t :=
      fun t ht => hkind' t ht
    have hlead : ∀ t, (adaptiveSlots coin known I per₁).slotRound t ≤ (U.block A).round →
        (adaptiveSlots coin known I per₁).leader t =
          (adaptiveSlots coin known I per₂).leader t := by
      intro t ht
      change (if adaptiveKind I per₁ t = 1 then coin t else known t) =
        (if adaptiveKind I per₂ t = 1 then coin t else known t)
      rw [hkind' t ht]
    exact PeriodAt.anchor (S := adaptiveSlots coin known I per₂) (ih fun i hi => h i (by omega))
      ha (AgreedAdvance.congr_slots (S₁ := adaptiveSlots coin known I per₁)
        (S₂ := adaptiveSlots coin known I per₂) (wavelength_two_le hws hwa) hA (fun _ => rfl)
        hlead hkind hadv)
  | @keep j st hp hn ih =>
    exact PeriodAt.keep (S := adaptiveSlots coin known I per₂) (ih fun i hi => h i (by omega)) hn

omit S in
/-- **SH10b, the sequences.** Two views that derived the state of every interval below `N`'s,
each reading its agreed output on its own adaptive schedule, derived the same periods there, by
strong induction on the interval: the sequences agree below an interval, so the second view's
derivation of its state is one on the first sequence's schedule (`periodAt_congr_per`), and
SH10a makes the two states one. -/
theorem adaptive_periods_agree {ws : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) {known : ℕ → Validator}
    {upd : UpdateRule BlockId} {k₀ N : ℕ} {V₁ V₂ : View Validator BlockId Payload U}
    {per₁ per₂ : ℕ → ℕ}
    (h₁ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₁) I K wa coin upd k₀ U V₁
        (wavelength ws wa) j st ∧ per₁ j = st.period)
    (h₂ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₂) I K wa coin upd k₀ U V₂
        (wavelength ws wa) j st ∧ per₂ j = st.period) :
    ∀ j, j ≤ intervalOf I N → per₁ j = per₂ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  obtain ⟨st₁, hp₁, he₁⟩ := h₁ j hj
  obtain ⟨st₂, hp₂, he₂⟩ := h₂ j hj
  have hp₂' := periodAt_congr_per (by omega) (by omega) hp₂ fun i hi => (ih i hi (by omega)).symm
  rw [he₁, he₂]
  exact congrArg ScanState.period
    (periodAt_unique (S := adaptiveSlots coin known I per₁) hwa hp₁ hp₂')

omit S in
/-- **SH10b, the verdicts.** The sequences agree below `N`'s interval (`adaptive_periods_agree`),
so the second view's verdict is one on the first sequence's schedule, whose kinds and leaders are
read at rounds at or below `N` only, and SH2 applies. -/
theorem adaptive_decided_unique {ws : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) {known : ℕ → Validator}
    {upd : UpdateRule BlockId} {k₀ N : ℕ} {V₁ V₂ : View Validator BlockId Payload U}
    {per₁ per₂ : ℕ → ℕ} (hN : ∀ b ∈ U.ids, (U.block b).round ≤ N) {k : ℕ} (hk : k ≤ N)
    (h₁ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₁) I K wa coin upd k₀ U V₁
        (wavelength ws wa) j st ∧ per₁ j = st.period)
    (h₂ : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₂) I K wa coin upd k₀ U V₂
        (wavelength ws wa) j st ∧ per₂ j = st.period)
    {v₁ v₂ : Option BlockId}
    (d₁ : Decided (S := adaptiveSlots coin known I per₁) (wavelength ws wa) U V₁ k v₁)
    (d₂ : Decided (S := adaptiveSlots coin known I per₂) (wavelength ws wa) U V₂ k v₂) :
    v₁ = v₂ := by
  have hper := adaptive_periods_agree hws hwa h₁ h₂
  have hNV : ∀ b ∈ V₂.ids, (U.block b).round ≤ N := fun b hb => hN b (V₂.subset_ids hb)
  have hkind' : ∀ t, t ≤ N → adaptiveKind I per₂ t = adaptiveKind I per₁ t :=
    fun t ht => (adaptiveKind_congr hper (r := t) ht).symm
  have hkind : ∀ t, (adaptiveSlots coin known I per₂).slotRound t ≤ N →
      (adaptiveSlots coin known I per₂).kind t = (adaptiveSlots coin known I per₁).kind t :=
    fun t ht => hkind' t ht
  have d₂' : Decided (S := adaptiveSlots coin known I per₁) (wavelength ws wa) U V₂ k v₂ :=
    decided_congr_slots (S₁ := adaptiveSlots coin known I per₂)
      (S₂ := adaptiveSlots coin known I per₁) hNV (fun _ => rfl) (fun t ht => by
        change (if adaptiveKind I per₂ t = 1 then coin t else known t) =
          (if adaptiveKind I per₁ t = 1 then coin t else known t)
        rw [hkind' t ht]) hkind d₂ hk
  exact AnchoredRule.decided_unique (S := adaptiveSlots coin known I per₁)
    (steelheadLaws (wavelength_two_le (by omega) (by omega))) trivial d₁ V₂ v₂ d₂'

/-! ## SH10c, SH10g, SH10d -/

omit S in
/-- **An interval with a committed control slot has an anchor** once every control slot of it
below that one has a verdict: the least committed one, at or below it. -/
theorem IntervalAnchor.of_committed {V : View Validator BlockId Payload U} {j k i₀ : ℕ}
    {A₀ : BlockId} (hpos₀ : 1 ≤ controlRound I K j k i₀)
    (hmem₀ : intervalOf I (controlRound I K j k i₀) = j)
    (hc₀ : ControlDecided I K wa coin j k U V i₀ (some A₀))
    (hall : ∀ i, 1 ≤ controlRound I K j k i → intervalOf I (controlRound I K j k i) = j →
      i < i₀ → ∃ v, ControlDecided I K wa coin j k U V i v) :
    ∃ i A, IntervalAnchor I K wa coin U V j k i A := by
  classical
  have hex : ∃ i, 1 ≤ controlRound I K j k i ∧ intervalOf I (controlRound I K j k i) = j ∧
      ∃ A, ControlDecided I K wa coin j k U V i (some A) := ⟨i₀, hpos₀, hmem₀, A₀, hc₀⟩
  have hle : Nat.find hex ≤ i₀ := Nat.find_le ⟨hpos₀, hmem₀, A₀, hc₀⟩
  obtain ⟨hpos, hmem, A, hA⟩ := Nat.find_spec hex
  refine ⟨_, A, hpos, hmem, hA, fun i' hpos' hmem' hlt => ?_⟩
  obtain ⟨v, hv⟩ := hall i' hpos' hmem' (by omega)
  cases v with
  | none => exact hv
  | some B => exact absurd ⟨hpos', hmem', B, hv⟩ (Nat.find_min hex hlt)

/-- **SH10c.** The least committed control slot of the interval is the anchor, over whose history
the agreed output advances, or there is none and every scanned control slot is skipped. -/
theorem exists_periodAt_succ {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j : ℕ} {st : ScanState}
    (hp : PeriodAt I K wa coin upd k₀ U V w j st)
    (hall : ∀ i, 1 ≤ controlRound I K j st.period i →
      intervalOf I (controlRound I K j st.period i) = j →
      ∃ v, ControlDecided I K wa coin j st.period U V i v) :
    ∃ st', PeriodAt I K wa coin upd k₀ U V w (j + 1) st' := by
  classical
  by_cases hex : ∃ i, 1 ≤ controlRound I K j st.period i ∧
    intervalOf I (controlRound I K j st.period i) = j ∧
    ∃ A, ControlDecided I K wa coin j st.period U V i (some A)
  · obtain ⟨i₀, hpos₀, hmem₀, A₀, hc₀⟩ := hex
    obtain ⟨i, A, hA⟩ :=
      IntervalAnchor.of_committed hpos₀ hmem₀ hc₀ fun i hpos hmem _ => hall i hpos hmem
    obtain ⟨next', last', hadv⟩ := AgreedAdvance.exists hw hA.mem_ids_U st.next st.lastCommit
    exact ⟨_, PeriodAt.anchor hp hA hadv⟩
  · refine ⟨st, PeriodAt.keep hp fun i hpos hmem => ?_⟩
    obtain ⟨v, hv⟩ := hall i hpos hmem
    cases v with
    | none => exact hv
    | some B => exact absurd ⟨i, hpos, hmem, B, hv⟩ hex

omit S in
/-- A round of interval `j` lies at or below `(j + 1) · I`. -/
theorem le_of_intervalOf {j r : ℕ} (hI : 0 < I) (h : intervalOf I r = j) : r ≤ (j + 1) * I := by
  unfold intervalOf at h
  have := (Nat.div_lt_iff_lt_mul hI).mp (show (r - 1) / I < j + 1 by omega)
  omega

omit S in
/-- A control slot of interval `j` lies at or below the boundary index. -/
theorem le_boundary_of_intervalOf {j k i : ℕ} (hI : 0 < I)
    (h : intervalOf I (controlRound I K j k i) = j) : i ≤ (j + 1) * I / k :=
  controlRound_le_boundary_iff.mp (le_of_intervalOf hI h)

/-- **SH10g.** Induction on the derivation: the initial period is in range, the failover's `1`
is, the warm-up keeps the period, and the update rule keeps the range. -/
theorem periodAt_mem_range {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) {j : ℕ} {st : ScanState}
    (hp : PeriodAt I K wa coin upd k₀ U V w j st) : 1 ≤ st.period ∧ st.period ≤ K := by
  induction hp with
  | zero => exact ⟨h₀, hK⟩
  | anchor _ _ _ ih =>
    dsimp only
    split_ifs
    · exact ⟨le_rfl, le_trans h₀ hK⟩
    · exact ih
    · exact hupd _ _ ih.1 ih.2
  | keep _ _ ih => exact ih

omit S in
/-- Under the clause at the scan's schedule a caught-up view settles every control slot of
interval `j`: the clause names a run past the first slot above the boundary, within `c + wa`
slots of it, each at most `K` rounds above the last. -/
theorem control_all_of_clause (hwa : 1 ≤ wa) (hI : 0 < I) {V : View Validator BlockId Payload U}
    {c N j k : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := controlSlots coin I K j k) U wa c wa N)
    (hV : V.CoversUpto N) (hN : MahiMahi.decisionRoundAt wa ((j + 1) * I + (c + wa) * K) ≤ N) :
    ∀ i, intervalOf I (controlRound I K j k i) = j →
      ∃ v, ControlDecided I K wa coin j k U V i v := by
  obtain ⟨b, hb, h⟩ := chainAllDecidedBelow hwa (controlRound_strictMono (I := I) (K := K) j k)
    hrun hV ((j + 1) * I / k + 1) (by
      rw [controlSlots_slotRound]
      have hle := controlRound_le_of_gt (I := I) (K := K) (j := j) (k := k)
        (i := (j + 1) * I / k + 1 + c + wa - 1) (by omega)
      rw [show (j + 1) * I / k + 1 + c + wa - 1 - (j + 1) * I / k = c + wa by omega] at hle
      unfold MahiMahi.decisionRoundAt at hN ⊢
      omega)
  intro i hi
  exact h i (by have := le_boundary_of_intervalOf hI hi; omega)

omit S [NeZero K] in
/-- The horizon condition of interval `j + 1` covers interval `j`'s. -/
theorem horizon_mono {c N j : ℕ}
    (h : MahiMahi.decisionRoundAt wa ((j + 1 + 1) * I + (c + wa) * K) ≤ N) :
    MahiMahi.decisionRoundAt wa ((j + 1) * I + (c + wa) * K) ≤ N := by
  unfold MahiMahi.decisionRoundAt at h ⊢
  have := Nat.mul_le_mul_right I (show j + 1 ≤ j + 1 + 1 by omega)
  omega

/-- **SH10d.** Induction on the interval: the period of each interval is in range (SH10g), the
clause at its control schedule settles the interval's control slots, and SH10c ends the scan. -/
theorem periodAt_of_clause (hwa : 1 ≤ wa) (hI : 0 < I) {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r)
    {upd : UpdateRule BlockId} {k₀ : ℕ} {V : View Validator BlockId Payload U} {c N : ℕ}
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    (hrun : ∀ j k, 1 ≤ k → k ≤ K →
      MahiMahi.UnpredictableRunWithin (S := controlSlots coin I K j k) U wa c wa N)
    (hV : V.CoversUpto N) (j : ℕ)
    (hN : MahiMahi.decisionRoundAt wa ((j + 1) * I + (c + wa) * K) ≤ N) :
    ∃ st, PeriodAt I K wa coin upd k₀ U V w (j + 1) st := by
  induction j with
  | zero =>
    exact exists_periodAt_succ hw PeriodAt.zero fun i _ hi =>
      control_all_of_clause hwa hI (hrun 0 k₀ h₀ hK) hV hN i hi
  | succ j ih =>
    obtain ⟨st, hst⟩ := ih (horizon_mono hN)
    obtain ⟨h1, h2⟩ := periodAt_mem_range h₀ hK hupd hst
    exact exists_periodAt_succ hw hst fun i _ hi =>
      control_all_of_clause hwa hI (hrun _ _ h1 h2) hV hN i hi

/-! ## SH10e, SH10n, SH10f -/

/-- **SH10e.** The anchor step of the sequence, its test read off. -/
theorem periodAt_one_of_anchor {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j i next' last' : ℕ} {st : ScanState} {A : BlockId}
    {hA : A ∈ U.ids} (hp : PeriodAt I K wa coin upd k₀ U V w j st)
    (ha : IntervalAnchor I K wa coin U V j st.period i A)
    (hadv : AgreedAdvance U w A hA st.next next' st.lastCommit last')
    (h : last' + I < controlRound I K j st.period i) :
    PeriodAt I K wa coin upd k₀ U V w (j + 1) ⟨1, next', last'⟩ := by
  have := PeriodAt.anchor hp ha hadv
  rwa [if_pos h] at this

/-- **SH10n.** The anchor step at interval `0`: the anchor lies at round `I` or below, so the
failover's test fails, and the warm-up keeps the period. -/
theorem periodAt_warmUp (hI : 0 < I) {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {i next' last' : ℕ} {st : ScanState} {A : BlockId}
    {hA : A ∈ U.ids} (hp : PeriodAt I K wa coin upd k₀ U V w 0 st)
    (ha : IntervalAnchor I K wa coin U V 0 st.period i A)
    (hadv : AgreedAdvance U w A hA st.next next' st.lastCommit last') :
    PeriodAt I K wa coin upd k₀ U V w 1 ⟨st.period, next', last'⟩ := by
  have hle := le_of_intervalOf hI ha.mem
  have := PeriodAt.anchor hp ha hadv
  rwa [if_neg (by omega), if_pos rfl] at this

omit S in
/-- A round of an interval past the first lies above the interval's first round less one. -/
theorem mul_add_one_le_of_intervalOf {j r : ℕ} (hI : 0 < I) (hj : 1 ≤ j)
    (h : intervalOf I r = j) : j * I + 1 ≤ r := by
  unfold intervalOf at h
  have := (Nat.le_div_iff_mul_le hI).mp (le_of_eq h.symm)
  have : 0 < j * I := Nat.mul_pos hj hI
  omega

/-- **The states are derivable as far as the control slots are settled**: once every scanned
control slot of the intervals up to `n` has a verdict in a view, at every period, the view derives
a state for every interval up to `n + 1`, SH10c at each step. -/
theorem exists_periodAt_of_settled {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {upd : UpdateRule BlockId}
    {k₀ : ℕ} {V : View Validator BlockId Payload U} {n : ℕ}
    (hall : ∀ j, j ≤ n → ∀ k i, 1 ≤ controlRound I K j k i →
      intervalOf I (controlRound I K j k i) = j → ∃ v, ControlDecided I K wa coin j k U V i v) :
    ∀ j, j ≤ n + 1 → ∃ st, PeriodAt I K wa coin upd k₀ U V w j st := by
  intro j
  induction j with
  | zero => exact fun _ => ⟨_, PeriodAt.zero⟩
  | succ j ih =>
    intro hj
    obtain ⟨st, hst⟩ := ih (by omega)
    exact exists_periodAt_succ hw hst fun i hpos hr => hall j (by omega) st.period i hpos hr

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

/-! ## SH10i, SH10j -/

/-- **SH10i.** Induction on the derivation: a slot consumed at an anchor is decided in the
anchor's history, which lies inside the view, and verdicts are monotone in the view. -/
theorem decided_of_lt_next {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j : ℕ} {st : ScanState}
    (hp : PeriodAt I K wa coin upd k₀ U V w j st) :
    ∀ s, 1 ≤ s → s < st.next → ∃ v, Decided w U V s v := by
  induction hp with
  | zero =>
    intro s h₁ h₂
    dsimp only at h₂
    omega
  | @anchor j i next' last' st A hA hp ha hadv ih =>
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
    (hp : PeriodAt I K wa coin upd k₀ U V w j st) (h₁ : 1 ≤ s)
    (hund : ∀ v, ¬ Decided w U V s v) : st.next ≤ s ∧ st.lastCommit ≤ s := by
  induction hp with
  | zero => exact ⟨h₁, Nat.zero_le _⟩
  | @anchor j i next' last' st A hA hp ha hadv ih =>
    exact hadv.le_of_stalled hw hid ha.mem_ids hund ih.1 ih.2
  | keep _ _ ih => exact ih

omit S in
/-- **SH10k.** Above round `I` the window starts at `top − I`, and the rounds from there to
`top − wa + 1` number at least `k`, so one of them is a multiple of `k`. -/
theorem window_resolves {K' k top : ℕ} (hk : 1 ≤ k) (hK : k ≤ K') (hwa : 1 ≤ wa)
    (hI : K' + wa - 2 ≤ I) (htop : I < top) :
    ∃ r, max 1 (top - I) ≤ r ∧ r + wa - 1 ≤ top ∧ IsAsync k r := by
  obtain ⟨q, m, hm, hqm⟩ : ∃ q m, m < k ∧ k * q + m = top - I + k - 1 :=
    ⟨(top - I + k - 1) / k, (top - I + k - 1) % k, Nat.mod_lt _ (by omega), Nat.div_add_mod _ _⟩
  exact ⟨k * q, by omega, by omega, Nat.mul_mod_right k q⟩

/-! ## SH14 -/

/-- The derivation of an interval's state ends in an anchor step or a keep step. -/
theorem PeriodAt.succ_cases {w : ℕ → ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {V : View Validator BlockId Payload U} {j : ℕ} {st' : ScanState}
    (h : PeriodAt I K wa coin upd k₀ U V w (j + 1) st') :
    (∃ (st : ScanState) (i : ℕ) (A : BlockId) (next' last' : ℕ) (hA : A ∈ U.ids),
        PeriodAt I K wa coin upd k₀ U V w j st ∧ IntervalAnchor I K wa coin U V j st.period i A ∧
        AgreedAdvance U w A hA st.next next' st.lastCommit last' ∧
        st' = ⟨if last' + I < controlRound I K j st.period i then 1
          else if j = 0 then st.period else upd A st.period, next', last'⟩) ∨
      ∃ st, PeriodAt I K wa coin upd k₀ U V w j st ∧ NoAnchor I K wa coin U V j st.period ∧
        st' = st := by
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
theorem lt_of_anchor_far {V : View Validator BlockId Payload U} (hI : 0 < I) {s j k i : ℕ}
    {A : BlockId} (hj : intervalOf I s + 1 < j) (hA : IntervalAnchor I K wa coin U V j k i A) :
    s + I < controlRound I K j k i := by
  have hsI := le_of_intervalOf hI (rfl : intervalOf I s = intervalOf I s)
  have hr : j * I + 1 ≤ controlRound I K j k i :=
    mul_add_one_le_of_intervalOf hI (by omega) hA.mem
  have h2 : (intervalOf I s + 1) * I ≤ (j - 1) * I := Nat.mul_le_mul_right I (by omega)
  have h3 : j * I = (j - 1) * I + I := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  omega

variable {ws : ℕ} {upd : UpdateRule BlockId} {k₀ : ℕ} {V : View Validator BlockId Payload U}
  {per : ℕ → ℕ}

/-- **The failover fires at every anchor more than `I` rounds above an undecided slot**: the state
the interval was derived under is stalled below the slot (SH10j), the advance stays there, so the
last commit lies below the slot and the test holds. The anchor is read at the period the view
derived for the interval, which every derivation of its state carries. -/
theorem period_eq_one_of_anchor_far (hws : 2 ≤ ws) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hI : 0 < I) {s j : ℕ} (h₁ : 1 ≤ s)
    (hund : ∀ v, ¬ Decided (wavelength ws wa) U V s v) (hj : intervalOf I s + 1 < j)
    {st' : ScanState} (hp' : PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) (j + 1) st')
    {k i : ℕ} {A : BlockId}
    (hk : ∀ st, PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j st → st.period = k)
    (hA : IntervalAnchor I K wa coin U V j k i A) : st'.period = 1 := by
  have hw2 : ∀ κ, 2 ≤ wavelength ws wa κ := wavelength_two_le hws (by omega)
  rcases hp'.succ_cases with ⟨st, i', A', next', last', hA', hp, hA'', hadv, rfl⟩ |
    ⟨st, hp, hn, rfl⟩
  · dsimp only
    have hst := stalled_below_undecided hw2 hid hp h₁ hund
    have hle := hadv.le_of_stalled hw2 hid hA''.mem_ids hund hst.1 hst.2
    have hfar := lt_of_anchor_far hI hj hA''
    rw [if_pos (by omega)]
  · rw [hk _ hp] at hn
    exact (hA.not_noAnchor hwa hn).elim

/-- **SH14.** If the slot is undecided, every anchor two or more intervals up lies more than `I`
rounds above it while the agreed output waits below it, so the failover fires at the anchored
interval and at every anchored interval after it, and the period is `1` from the next interval on,
up to the run; the run's rounds then carry wave `wa`, its coins commit their candidates directly,
and the drain (SH9) decides every slot below the run, the slot among them. -/
theorem output_liveness (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    {b : ℕ}
    (hper : ∀ j, j ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j st ∧ per j = st.period)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r)
    {s j₁ i₁ : ℕ} {A : BlockId} (h₁ : 1 ≤ s) (hs : intervalOf I s + 1 < j₁)
    (hA : IntervalAnchor I K wa coin U V j₁ (per j₁) i₁ A) (hb : (j₁ + 1) * I < b)
    (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (wavelength ws wa) U V s v := by
  classical
  by_cases hdec : ∃ v, Decided (wavelength ws wa) U V s v
  · exact hdec
  replace hdec : ∀ v, ¬ Decided (wavelength ws wa) U V s v := fun v hv => hdec ⟨v, hv⟩
  -- the run lies in intervals past the anchored one, all of them derived
  have hbj : j₁ + 1 ≤ intervalOf I b := le_intervalOf_of_lt hI hb
  have hbN : intervalOf I b ≤ intervalOf I (b + wa - 1) := intervalOf_mono (by omega)
  -- every derivation of the anchored interval's state carries the period the view derived
  have hk : ∀ st, PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j₁ st →
      st.period = per j₁ := by
    intro st hst
    obtain ⟨st₁, hp₁, he₁⟩ := hper j₁ (by omega)
    rw [he₁]
    exact congrArg ScanState.period (periodAt_unique hwa hst hp₁)
  -- the period is 1 from the interval after the anchored one up to the run's
  have hone : ∀ n, j₁ + 1 + n ≤ intervalOf I (b + wa - 1) → per (j₁ + 1 + n) = 1 := by
    intro n
    induction n with
    | zero =>
      intro hn
      obtain ⟨st', hp', he'⟩ := hper (j₁ + 1) hn
      change per (j₁ + 1) = 1
      rw [he']
      exact period_eq_one_of_anchor_far hws hwa hid hI h₁ hdec hs hp' hk hA
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      obtain ⟨st', hp', he'⟩ := hper (j₁ + 1 + n + 1) hn
      change per (j₁ + 1 + n + 1) = 1
      rw [he']
      rcases hp'.succ_cases with ⟨st, i, A', next', last', hA', hp, hA'', hadv, rfl⟩ |
        ⟨st, hp, _, rfl⟩
      · exact period_eq_one_of_anchor_far hws hwa hid hI h₁ hdec (by omega) hp'
          (fun st'' hp'' => congrArg ScanState.period (periodAt_unique hwa hp'' hp)) hA''
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
  have hasync : ∀ i, i < wa → S.kind (b + i) = 1 := by
    intro i hi
    rw [hkind]
    unfold adaptiveKind
    rw [hper1 i hi, periodicKind_one]
  have hlead' : ∀ i, i < wa → S.leader (b + i) = coin (b + i) :=
    fun i hi => hlead (b + i) (hasync i hi)
  -- the run's candidates commit directly in a view holding their decision rounds
  have hrun : ∀ i, i < wa → ∃ L, Decided (wavelength ws wa) U V (b + i) (some L) := by
    intro i hi
    obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hgood i hi)
    refine ⟨L, Decided.directCommit ⟨hL, by rw [hid]; exact hLr, hLc.trans (hlead' i hi).symm⟩ ?_⟩
    change MahiMahi.DirectCommitIn U V (wavelength ws wa (S.kind (b + i))) L (S.slotRound (b + i))
    rw [hid, hasync i hi, wavelength_one]
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
    (fun t => Nat.le_of_succ_le (wavelength_two_le hws (by omega) (S.kind t)))
    (fun t => wavelength_le hle (S.kind t)) hid hrun s hsb

/-! ## SH14c, SH14b -/

omit S in
/-- A round strictly above `j · I` and at most `(j + 1) · I` lies in interval `j`. -/
theorem intervalOf_eq_of_mul_lt_le {j r : ℕ} (h₁ : j * I < r) (h₂ : r ≤ (j + 1) * I) :
    intervalOf I r = j := by
  unfold intervalOf
  exact Nat.div_eq_of_lt_le (by omega) (by omega)


omit S [NeZero K] in
/-- **The first control round is the round of the first control slot of the interval**: at a
period from `1` to `I`, slot `j · I / k + 1` lies in interval `j`, at round `1` or above, and no
control slot below it lies in the interval at round `1` or above. -/
theorem firstControlRound_eq {j k : ℕ} (hk : 1 ≤ k) (hkI : k ≤ I) :
    controlRound I K j k (j * I / k + 1) = firstControlRound I j k ∧
      1 ≤ firstControlRound I j k ∧ intervalOf I (firstControlRound I j k) = j ∧
      ∀ i, i < j * I / k + 1 → 1 ≤ controlRound I K j k i →
        intervalOf I (controlRound I K j k i) ≠ j := by
  have hI : 0 < I := by omega
  have hmul : (j + 1) * I = j * I + I := by rw [Nat.add_mul, Nat.one_mul]
  -- the first control round lies in the interval
  have hlo : j * I < firstControlRound I j k := by
    unfold firstControlRound
    rw [Nat.add_mul, Nat.one_mul]
    exact lt_of_lt_of_le (Nat.lt_div_mul_add hk) (by omega)
  have hhi : firstControlRound I j k ≤ (j + 1) * I := by
    unfold firstControlRound
    rw [Nat.add_mul, Nat.one_mul, hmul]
    exact Nat.add_le_add (Nat.div_mul_le_self _ _) hkI
  have hidx : j * I / k + 1 ≤ (j + 1) * I / k := by
    rw [Nat.le_div_iff_mul_le hk]
    exact hhi
  refine ⟨controlRound_of_le hidx, by omega, intervalOf_eq_of_mul_lt_le hlo hhi, ?_⟩
  intro i hi hpos hmem
  have hle : controlRound I K j k i = i * k := controlRound_of_le (by omega)
  have h1 : i * k ≤ j * I / k * k := Nat.mul_le_mul_right k (by omega)
  have h2 := Nat.div_mul_le_self (j * I) k
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [Nat.zero_mul, Nat.zero_div] at h1
    omega
  · have := mul_add_one_le_of_intervalOf hI hj hmem
    omega

/-- **SH14c.** The good coin at interval `j`'s first control round commits that control slot, at
the period the view derived for the interval, and no control slot of the interval lies below it,
so the interval has its anchor; the `wa` good coins above the interval are the run SH14 needs. -/
theorem output_liveness_of_runs (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r) {b : ℕ}
    (hper : ∀ j', j' ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j' st ∧ per j' = st.period)
    {s j : ℕ} (h₁ : 1 ≤ s) (hs : intervalOf I s + 1 < j) (hk : 1 ≤ per j) (hkI : per j ≤ I)
    (hgood : coin (firstControlRound I j (per j)) ∈
      MahiMahi.goodAt U wa (firstControlRound I j (per j)))
    (hb : (j + 1) * I < b) (hgoodb : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (wavelength ws wa) U V s v := by
  obtain ⟨hcr, hpos, hmem, hnone⟩ := firstControlRound_eq (I := I) (K := K) (j := j) hk hkI
  -- the coin at the first control round commits the first control slot
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hgood
  have hc : ControlDecided I K wa coin j (per j) U V (j * I / per j + 1) (some L) := by
    refine MahiMahi.Decided.directCommit (S := controlSlots coin I K j (per j)) ?_ ?_
    · exact ⟨hL, by rw [controlSlots_slotRound, hcr]; exact hLr,
        by rw [controlSlots_leader, hcr]; exact hLc⟩
    · change MahiMahi.DirectCommitIn U V wa L
        ((controlSlots coin I K j (per j)).slotRound (j * I / per j + 1))
      rw [controlSlots_slotRound, hcr]
      refine MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_)
      have := le_of_intervalOf hI hmem
      unfold MahiMahi.decisionRoundAt
      omega
  obtain ⟨i₁, A, hA⟩ := IntervalAnchor.of_committed (by rw [hcr]; exact hpos)
    (by rw [hcr]; exact hmem) hc fun i hpos' hi hlt => absurd hi (hnone i hlt hpos')
  exact output_liveness hws hle hwa hid hkind hI hper hlead h₁ hs hA hb hgoodb hV

/-- **SH14b.** At the second interval after the slot's, the clause at the interval's own control
schedule places a run of `wa` good control slots inside the interval: the run's first slot commits,
and the run settles every control slot below it (SH7a), so the interval has an anchor at or below
that slot; the clause at period `1` in the next interval, whose control schedule is every round up
to its boundary, places the run of rounds SH14 needs. -/
theorem all_decided (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa) (hid : ∀ t, S.slotRound t = t)
    (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r)
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {c N : ℕ} (hcK : (c + wa) * K ≤ I)
    (hrun : ∀ j k, 1 ≤ k → k ≤ K →
      MahiMahi.UnpredictableRunWithin (S := controlSlots coin I K j k) U wa c wa N)
    (hV : V.CoversUpto N)
    (hper : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j st ∧ per j = st.period)
    (s : ℕ) (h₁ : 1 ≤ s)
    (hN : MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + c + wa) ≤ N) :
    ∃ v, Decided (wavelength ws wa) U V s v := by
  have hKpos : 0 < K := pos_of_neZero
  have hcwa : c + wa ≤ (c + wa) * K := Nat.le_mul_of_pos_right (c + wa) hKpos
  obtain ⟨j₂, hj₂⟩ : ∃ j₂, j₂ = intervalOf I s + 2 := ⟨_, rfl⟩
  have hmul3 : (j₂ + 1) * I = j₂ * I + I := by rw [Nat.add_mul, Nat.one_mul]
  have hmul4 : (j₂ + 1 + 1) * I = (j₂ + 1) * I + I := by rw [Nat.add_mul, Nat.one_mul]
  rw [show intervalOf I s + 3 = j₂ + 1 by omega] at hN
  unfold MahiMahi.decisionRoundAt at hN
  -- the period the view derived for interval j₂ lies in range
  have hj₂N : j₂ ≤ intervalOf I N := by
    rw [← intervalOf_eq_of_mul_lt_le (j := j₂) (r := (j₂ + 1) * I) (by rw [hmul3]; omega) le_rfl]
    exact intervalOf_mono (by omega)
  obtain ⟨st₂, hp₂, he₂⟩ := hper j₂ hj₂N
  obtain ⟨hk1, hk2⟩ := periodAt_mem_range h₀ hK hupd hp₂
  obtain ⟨k, hkdef⟩ : ∃ k, st₂.period = k := ⟨_, rfl⟩
  rw [hkdef] at hk1 hk2 he₂
  -- the clause at the interval's schedule places a run of wa good control slots inside it
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ = j₂ * I / k + 1 := ⟨_, rfl⟩
  have hi₀le : i₀ + c + wa - 1 ≤ (j₂ + 1) * I / k := by
    rw [Nat.le_div_iff_mul_le hk1, hmul3]
    have h1 : (j₂ * I / k + c + wa) * k ≤ j₂ * I + (c + wa) * k := by
      simp only [Nat.add_mul]
      have := Nat.div_mul_le_self (j₂ * I) k
      omega
    have h2 : (c + wa) * k ≤ (c + wa) * K := Nat.mul_le_mul_left _ hk2
    have h3 : (i₀ + c + wa - 1) * k ≤ (j₂ * I / k + c + wa) * k :=
      Nat.mul_le_mul_right k (by have := Nat.zero_le (j₂ * I / k); omega)
    omega
  obtain ⟨k', hk'1, hk'2, hg⟩ := hrun j₂ k hk1 hk2 i₀ (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := controlSlots coin I K j₂ k) (by omega),
      controlSlots_slotRound]
    have := controlRound_le_boundary_iff (I := I) (K := K) (j := j₂) (k := k)
      (i := i₀ + c + wa - 1) |>.mpr hi₀le
    unfold MahiMahi.decisionRoundAt
    omega)
  -- the run lies inside the interval: its slots are up to the boundary index and above j₂ · I
  have hrun_le : ∀ u, u < wa → k' + u ≤ (j₂ + 1) * I / k := fun u hu => by
    have := Nat.zero_le (j₂ * I / k)
    have := Nat.zero_le ((j₂ + 1) * I / k)
    omega
  have hlt_all : ∀ u, u < wa → j₂ * I < controlRound I K j₂ k (k' + u) := by
    intro u hu
    rw [controlRound_of_le (hrun_le u hu)]
    have h1 := Nat.lt_div_mul_add (a := j₂ * I) hk1
    have h2 : (j₂ * I / k + 1) * k ≤ (k' + u) * k := Nat.mul_le_mul_right k (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have hround_mem : ∀ u, u < wa → intervalOf I (controlRound I K j₂ k (k' + u)) = j₂ :=
    fun u hu => intervalOf_eq_of_mul_lt_le (hlt_all u hu)
      (controlRound_le_boundary_iff (I := I) (K := K) |>.mpr (hrun_le u hu))
  -- the run's first slot commits: its round's coin is good
  have hg0 := hg 0 (by omega)
  rw [controlSlots_leader, MahiMahi.good, controlSlots_slotRound] at hg0
  have hcov0 : MahiMahi.decisionRoundAt wa (controlRound I K j₂ k (k' + 0)) ≤ N := by
    have := controlRound_le_boundary_iff (I := I) (K := K) |>.mpr (hrun_le 0 (by omega))
    unfold MahiMahi.decisionRoundAt
    omega
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hg0
  have hc : ControlDecided I K wa coin j₂ k U V (k' + 0) (some L) :=
    MahiMahi.Decided.directCommit (S := controlSlots coin I K j₂ k) ⟨hL, hLr, hLc⟩
      (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono hcov0))
  -- and the run settles every control slot below it
  have hcovrun : MahiMahi.decisionRoundAt wa
      ((controlSlots coin I K j₂ k).slotRound (k' + wa - 1)) ≤ N := by
    rw [controlSlots_slotRound, show k' + wa - 1 = k' + (wa - 1) by omega]
    have := controlRound_le_boundary_iff (I := I) (K := K) |>.mpr (hrun_le (wa - 1) (by omega))
    unfold MahiMahi.decisionRoundAt
    omega
  have hall := allDecidedBelowOfGoodRun (by omega) (controlRound_strictMono (I := I) (K := K) j₂ k)
    hg (hV.mono hcovrun)
  obtain ⟨i₁, A, hA⟩ := IntervalAnchor.of_committed
    (by have := hlt_all 0 (by omega); omega) (hround_mem 0 (by omega)) hc
    fun i _ _ hi => hall i hi
  rw [← he₂] at hA
  -- the clause at period 1 in the next interval places the run of rounds SH14 needs
  obtain ⟨b, hb1, hb2, hgb⟩ := hrun (j₂ + 1) 1 le_rfl hKpos ((j₂ + 1) * I + 1) (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := controlSlots coin I K (j₂ + 1) 1)
      (by omega), controlSlots_slotRound]
    have hle : (j₂ + 1) * I + 1 + c + wa - 1 ≤ (j₂ + 1 + 1) * I / 1 := by
      rw [Nat.div_one, hmul4]
      omega
    rw [controlRound_of_le hle, Nat.mul_one]
    unfold MahiMahi.decisionRoundAt
    omega)
  have hb_le : ∀ u, u < wa → b + u ≤ (j₂ + 1 + 1) * I / 1 := by
    intro u hu
    rw [Nat.div_one, hmul4]
    omega
  have hgoodb : ∀ u, u < wa → coin (b + u) ∈ MahiMahi.goodAt U wa (b + u) := by
    intro u hu
    have := hgb u hu
    rw [controlSlots_leader, MahiMahi.good, controlSlots_slotRound,
      controlRound_of_le (hb_le u hu), Nat.mul_one] at this
    exact this
  refine output_liveness hws hle hwa hid hkind hI (b := b) (fun j hj => hper j ?_) hlead h₁
    (by omega) hA (by omega) hgoodb (hV.mono (by
      unfold MahiMahi.decisionRoundAt
      omega))
  exact le_trans hj (intervalOf_mono (by omega))

end Slots

end Steelhead

end LeanDag
