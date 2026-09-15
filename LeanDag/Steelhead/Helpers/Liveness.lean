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

/-- **SH6a.** The bridge certifies the slot's candidate from every reliable block at its decision
round, which is the direct commit, in the view and at the slot's own wave. -/
theorem commitsOfSynchrony {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N k : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hR : R ≤ S.slotRound k)
    (hN : ∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧
      MahiMahi.DirectCommitIn U V (w (S.slotRound k)) L (S.slotRound k) ∧
      Decided w U V k (some L) := by
  obtain ⟨-, -, -, -, h⟩ := Timed.live_of_coverage (shSupport w) (shSupport_ofCoverage hw)
    (isQuorum_core hT hcard) hs hpop S V (lo := k) (K := k + 1) hV hR
    (fun j hj => hN j (Nat.lt_succ_iff.mp hj))
  obtain ⟨hpopk, hcert⟩ := h k le_rfl (Nat.lt_succ_self k) hlead
  obtain ⟨L, hL, hin⟩ := shSupport_directCommitIn (fun r => by have := hw r; omega) S V
    hcard hpopk hcert (fun b hb hbr => hV b hb (le_trans hbr (hN k le_rfl))) hlead
  exact ⟨L, hL, hin, Decided.directCommit hL hin⟩

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

/-- **SH6f.** The least committed slot at or above the floor is the anchor: the reliably led slot
commits directly (SH6a), so there is one, and every eligible slot below it is decided but not
committed, a skip. The indirect rule then decides the slot. -/
theorem decidedOfReliableAboveFloor {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t) {T : Finset Validator}
    {V : View Validator BlockId Payload U} {R N k a : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hR : R ≤ k) (hka : k + w k ≤ a)
    (hlead : S.leader a ∈ T) (hdec : ∀ j, k + w k ≤ j → j < a → ∃ v, Decided w U V j v)
    (hN : ∀ j, j ≤ a → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) : ∃ v, Decided w U V k v := by
  classical
  -- the reliably led slot commits
  obtain ⟨A, -, -, hA⟩ := commitsOfSynchrony hw hT hcard hs hpop (by rw [hid]; omega) hN hV hlead
  -- the least committed slot at or above the floor
  have hex : ∃ j, k + w k ≤ j ∧ ∃ A, Decided w U V j (some A) := ⟨a, hka, A, hA⟩
  obtain ⟨hkj, A', hA'⟩ : k + w k ≤ Nat.find hex ∧ ∃ A, Decided w U V (Nat.find hex) (some A) :=
    Nat.find_spec hex
  have hja : Nat.find hex ≤ a := Nat.find_le ⟨hka, A, hA⟩
  -- every eligible slot between the floor and it is decided but not committed, so skipped
  have hmid : ∀ i', k < i' → i' < Nat.find hex →
      (fun sr i j => sr i + w (sr i) ≤ sr j) S.slotRound k i' → Decided w U V i' none := by
    intro i' _ hi'j helig
    simp only [hid] at helig
    have hnc : ¬ ∃ C, Decided w U V i' (some C) := fun hc => Nat.find_min hex hi'j ⟨helig, hc⟩
    obtain ⟨v, hv⟩ := hdec i' helig (by omega)
    cases v with
    | none => exact hv
    | some C => exact absurd ⟨C, hv⟩ hnc
  obtain ⟨v, hv⟩ := indirect (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
    (fun r => by have := hw r; omega) S V k (Nat.find hex) A' (by simp only [hid]; exact hkj) hA'
    hmid
  exact ⟨v, hv S rfl rfl hA' hmid⟩

/-! ## SH6c, SH6e -/

/-- **SH6c.** Every reliable block at the vote round blames a slot whose leader has no block at
the slot's round, since no candidate lies in any cone, and a view holding that round holds a
quorum of them. -/
theorem skipsCrashed {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hcrash : ∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k)
    (hpop : PopulatedOn U T (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k)))
    (hV : V.CoversUpto (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k))) :
    Decided w U V k none := by
  refine Decided.directSkip ?_
  change MahiMahi.DirectSkipIn U V (w (S.slotRound k)) (S.leader k) (S.slotRound k)
  unfold MahiMahi.DirectSkipIn HoldsAtLeast
  refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
  obtain ⟨q, hq, hqc, hqr⟩ := hpop v hv
  refine mem_heldAuthors.mpr ⟨q, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hq, hqr⟩, ?_⟩,
    hV q hq (le_of_eq hqr), hqc⟩
  unfold MahiMahi.Blames
  refine Finset.eq_empty_of_forall_notMem fun L hL => ?_
  obtain ⟨hLids, hLr, hLc, -⟩ := MahiMahi.mem_candidatesAt.mp hL
  exact hcrash L hLids hLr hLc

omit S in
/-- A block reaching the only block of its author at a round votes for it: `Votes` asks for the
least candidate of that author and round in the cone, and there is one. -/
theorem votes_of_reaches_of_unique {U : BlockUniverse Validator BlockId Payload} {q L : BlockId}
    (hq : q ∈ U.ids) (hL : L ∈ U.ids)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L)
    (h : Reaches U q L) : MahiMahi.Votes U q L := by
  refine ⟨MahiMahi.mem_candidatesAt.mpr ⟨hL, rfl, rfl, (mem_history_iff hq).mpr h⟩, ?_⟩
  intro L' hL' hlt
  obtain ⟨hL'ids, hL'r, hL'c, -⟩ := MahiMahi.mem_candidatesAt.mp hL'
  rw [huniq L' hL'ids hL'r hL'c] at hlt
  exact lt_irrefl _ hlt

omit S [LinearOrder BlockId] in
/-- Under synchrony from `R`, a block one reliable round-`R` block references lies in the cone of
every reliable block at the rounds past `R` the reliable set populates: each reliable block
references every reliable block one round down, one of which reaches it. -/
theorem reaches_of_synchronised_of_ref {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} {R N : ℕ} {L q : BlockId} (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = R) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) :
    ∀ c ∈ U.ids, R + 1 ≤ (U.block c).round → (U.block c).round ≤ N →
      (U.block c).creator ∈ T → Reaches U c L := by
  suffices H : ∀ m, R + 1 ≤ m → m ≤ N → ∀ c ∈ U.ids, (U.block c).round = m →
      (U.block c).creator ∈ T → Reaches U c L by
    intro c hc h1 h2 hcT
    exact H _ h1 h2 c hc rfl hcT
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _ c hc hcr hcT
    exact Reaches.trans (Reaches.single (hs R le_rfl c hc hcr hcT q hq hqr hqT))
      (Reaches.single hqL)
  | succ m hRm ih =>
    intro hmN c hc hcr hcT
    obtain ⟨v, hv⟩ := MahiMahi.nonempty_of_quorum hcard
    obtain ⟨b, hb, hbc, hbr⟩ := hpop m (by omega) (by omega) v hv
    exact Reaches.trans (Reaches.single (hs m (by omega) c hc hcr hcT b hb hbr (hbc ▸ hv)))
      (ih (by omega) b hb hbr (hbc ▸ hv))

/-- **SH6e.** Synchrony carries the candidate into every reliable cone from two rounds up; the
reliable voters vote for it, the leader's only block at its round; every reliable block at the
decision round references all of them and so certifies; and a view holding the decision round
holds those certificates. -/
theorem commitsOfDissemination {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ} {L q : BlockId}
    (hw : 4 ≤ w (S.slotRound k)) (hcard : quorumCard Validator ≤ T.card)
    (hL : IsLeaderBlock U k L)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = S.slotRound k →
      (U.block L').creator = S.leader k → L' = L)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = S.slotRound k + 1) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) (hs : SynchronisedOn U T (S.slotRound k + 1))
    (hpop : ∀ r, S.slotRound k + 1 ≤ r →
      r ≤ MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k) → PopulatedOn U T r)
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k))) :
    Decided w U V k (some L) := by
  have hreach := reaches_of_synchronised_of_ref hcard hs hpop hq hqr hqT hqL
  have huniq' : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L :=
    fun L' h1 h2 h3 => huniq L' h1 (h2.trans hL.2.1) (h3.trans hL.2.2)
  -- every reliable block at the decision round certifies L
  have hcert : ∀ C ∈ U.ids,
      (U.block C).round = MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k) →
      (U.block C).creator ∈ T →
      C ∈ MahiMahi.certificates U (w (S.slotRound k)) L (S.slotRound k) := by
    intro C hC hCr hCT
    refine mem_certificatesAt.mpr ⟨hC, hCr, ?_⟩
    unfold CarriesVotes
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k))
      (by unfold MahiMahi.votingRound; omega)
      (by unfold MahiMahi.votingRound MahiMahi.decisionRoundAt; omega) v hv
    refine mem_creatorsOf.mpr ⟨b, mem_carriedVotes.mpr ⟨?_, ?_⟩, hbc⟩
    · refine hs (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k))
        (by unfold MahiMahi.votingRound; omega) C hC ?_ hCT b hb hbr (hbc ▸ hv)
      rw [hCr]
      unfold MahiMahi.votingRound MahiMahi.decisionRoundAt
      omega
    · refine votes_of_reaches_of_unique hb hL.1 huniq' (hreach b hb ?_ ?_ (hbc ▸ hv))
      · rw [hbr]; unfold MahiMahi.votingRound; omega
      · rw [hbr]; unfold MahiMahi.votingRound MahiMahi.decisionRoundAt; omega
  -- so L is directly committed, and the view holds the certificates
  have hdc : MahiMahi.DirectCommit U (w (S.slotRound k)) L (S.slotRound k) := by
    unfold MahiMahi.DirectCommit
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨C, hC, hCc, hCr⟩ := hpop _ (by unfold MahiMahi.decisionRoundAt; omega) le_rfl v hv
    exact mem_creatorsOf.mpr ⟨C, hcert C hC hCr (hCc ▸ hv), hCc⟩
  exact Decided.directCommit hL (MahiMahiProperties.directCommitIn_of_coversUpto hdc hV)

end Slots

/-! ## SH7 — the chain -/

/-- At the identity schedule a run of `wa` slots spans, at wave `wa`. -/
theorem chainSpansEligible {wa : ℕ} (hwa : 1 ≤ wa) (coin : ℕ → Validator) :
    (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).SpansEligible
      (S := chainSlots coin) wa := by
  have := (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).spansEligible_of_identity
    (S := chainSlots coin) (fun _ => rfl) (w := wa - 1) (fun _ => le_rfl)
  rwa [Nat.sub_add_cancel hwa] at this

/-- **SH7c.** The core's descent below a run of direct commits, at the chain schedule: the run's
commits are direct, and a view holding their decision rounds holds their certificates. -/
theorem chainAllDecidedBelowOfRun {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {b : ℕ}
    (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  refine AnchoredRule.decided_below_of_run (S := chainSlots coin)
    (fun hi h => MahiMahi.exists_least (S := chainSlots coin) hi h) hwa
    (chainSpansEligible hwa coin) (Led := fun j => coin j ∈ MahiMahi.goodAt U wa j) hgood
    fun j _ hj2 hj => ?_
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hj
  refine ⟨L, MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hL, hLr, hLc⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_))⟩
  change MahiMahi.decisionRoundAt wa j ≤ MahiMahi.decisionRoundAt wa (b + wa - 1)
  unfold MahiMahi.decisionRoundAt
  omega

/-- **SH7a.** MM3c at the chain schedule, in any view caught up to the horizon: the clause names
a run past `r`, and SH7c settles everything below it. -/
theorem chainAllDecidedBelow {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N)
    (hV : V.CoversUpto N) (r : ℕ) (hr : MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun r (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := chainSlots coin) hwa]; exact hr)
  refine ⟨k', hk1, chainAllDecidedBelowOfRun hwa hgood (hV.mono ?_)⟩
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
