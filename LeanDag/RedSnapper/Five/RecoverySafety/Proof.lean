import LeanDag.RedSnapper.Five.RecoverySafety.Statement
import LeanDag.RedSnapper.Helpers.Freeze

/-!
# Recovery safety — proof

Generated proof layer; not part of the audit surface. Uniqueness is
least-index logic plus antisymmetry. The reflection claim is
`frozen_stance_eq_ack` — the certificate's correct core reads `ack tx`
wherever its markers are visible — intersected with the marker quorum
(`|F ∩ S| ≥ 2f + 1` needs `Five`); its uniqueness half and the winner
claim are `not_atLeastV_of_disjoint` counts at any committee; the
release claim is the reflection claim's contrapositive. The hidden-release
claim is `no_unlock_of_eligible`, the `⊥` core against the winner's
frozen supporters, which RS8 consumes too.
`recoveryReflects_at` re-packages the reflection claim at a resolution,
the shape RS8 consumes.
-/

namespace LeanDag

namespace RedSnapper

namespace RecoverySafety

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

theorem resolutionUnique {A : Anchors U} {prio : Tx → Tx → Prop}
    (hord : IsLinearOrder Tx prio) : ResolutionUnique U A prio := by
  constructor
  · intro o i j i' j' h h'
    have hi : i = i' := by
      rcases lt_trichotomy i i' with hlt | heq | hgt
      · obtain ⟨a, hlk, ht⟩ := h.1.1
        exact absurd ht (h'.1.2 i hlt a hlk)
      · exact heq
      · obtain ⟨a, hlk, ht⟩ := h'.1.1
        exact absurd ht (h.1.2 i' hgt a hlk)
    subst hi
    refine ⟨rfl, ?_⟩
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · obtain ⟨aₖ, a, hlk, hla, hq⟩ := h.2.2.1
      exact absurd hq (h'.2.2.2 j hlt aₖ a hlk hla)
    · exact heq
    · obtain ⟨aₖ, a, hlk, hla, hq⟩ := h'.2.2.1
      exact absurd hq (h.2.2.2 j' hgt aₖ a hlk hla)
  · intro aₖ a o tx tx' he hmin he' hmin'
    haveI := hord
    exact antisymm (hmin tx' he') (hmin' tx he)

theorem recoveryReflects (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U)
    (hfive : Five Validator) : RecoveryReflects U := by
  intro o aₖ a tx ha hq hin ⟨C, hC, hfull⟩
  subst hin
  have hn := F.card_validators
  have h5 := hfive.card_validators
  obtain ⟨S, hS, hk, hfroz⟩ := frozen_stance_eq_ack hmove hfd hC hfull
  -- the marker quorum's overlap with the certificate's core: frozen and
  -- standing at tx
  obtain ⟨t, htS, hfr_t, hcard⟩ := atLeastV_inter (S := S) hq
  have hhalf : half Validator ≤ t.card := by
    unfold quorum at hk hcard
    unfold half
    omega
  have hstance : ∀ v ∈ t, Frozen U aₖ v (T.input tx) a ∧
      StanceIs U v (T.input tx) a (some (Stance.ack tx)) := fun v hv =>
    ⟨hfr_t v hv, hfroz v (htS hv) aₖ a ha (hfr_t v hv)⟩
  have hne : t.Nonempty := Finset.card_pos.mp (by
    have := half_pos (Validator := Validator)
    omega)
  obtain ⟨v₀, hv₀⟩ := hne
  have helig : EligibleFive U aₖ a (T.input tx) tx := by
    refine ⟨candidate_of_stance_ack hfd (hS (htS hv₀)) (hstance v₀ hv₀).2,
      t, hstance, hhalf⟩
  refine ⟨helig, fun tx' he' => ?_⟩
  by_contra hne'
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  refine not_atLeastV_of_disjoint hcount (fun v hP hvS => ?_) he'.2
  obtain ⟨hfr, hst⟩ := hP
  have hack := hfroz v hvS aₖ a ha hfr
  have := stanceIs_unique hst hack
  simp only [Option.some.injEq, Stance.ack.injEq] at this
  exact hne' this

theorem recoverySafetyBot (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U)
    (hfive : Five Validator) : RecoverySafetyBot U := by
  intro o aₖ a ha hq hempty tx hin C hC hfull
  exact hempty tx (recoveryReflects hmove hfd hfive o aₖ a tx ha hq hin
    ⟨C, hC, hfull⟩).1

theorem recoverySafetyWin (hfd : FreezeDiscipline U) : RecoverySafetyWin U := by
  intro o aₖ a tx ha helig tx' hconf C hC hround hfull'
  have hn := F.card_validators
  obtain ⟨hcand, w, hw, hwcard⟩ := helig
  have ho : T.input tx = o := hcand.2.1
  subst ho
  -- the winner's correct supporters: at least f + 1, frozen at `ack tx`
  have hbyz := F.card_byzantine
  classical
  set S' : Finset Validator := w.filter (· ∈ (Correct : Finset Validator)) with hS'
  have hS'sub : ∀ v ∈ S', v ∈ (Correct : Finset Validator) := fun v hv =>
    (Finset.mem_filter.mp hv).2
  have hS'card : half Validator ≤ S'.card + F.f := by
    have hsplit : w ⊆ S' ∪ F.byzantine := by
      intro v hv
      by_cases hcv : v ∈ (Correct : Finset Validator)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hcv⟩)
      · exact Finset.mem_union_right _ (by simpa [Correct] using hcv)
    have h2 := Finset.card_le_card hsplit
    have h3 := Finset.card_union_le S' F.byzantine
    omega
  have hcount : Fintype.card Validator < S'.card + quorum Validator := by
    unfold half at hS'card
    unfold quorum
    omega
  refine not_atLeast_of_disjoint hcount ?_ hfull'
  intro q hq hfv hvS'
  set v := (U.block q).author with hv
  have hvw : v ∈ w := (Finset.mem_filter.mp hvS').1
  have hvc : v ∈ (Correct : Finset Validator) := hS'sub _ hvS'
  obtain ⟨hfr, hst⟩ := hw v hvw
  obtain ⟨m, hm, ham, hrm, hmk⟩ := hfr
  have hcm : (U.block m).author ∈ (Correct : Finset Validator) := ham.symm ▸ hvc
  -- the marker's declaration is `ack tx`, read at the electing block
  obtain ⟨s, hds, hsta⟩ := stance_at_of_frozen hfd hm ha hcm hrm hmk
  have hs : s = Stance.ack tx := by
    have := stanceIs_unique (ham ▸ hsta) hst
    exact Option.some.inj this
  subst hs
  -- the rival vote block sits above the marker and reads the same value
  have hqid : q ∈ U.ids := U.complete C hC q hq
  have hqr : (U.block q).round + 1 = (U.block C).round := round_of_mem_parents hC hq
  have hra : (U.block m).round ≤ (U.block a).round := round_le_of_reaches ha hrm
  have hrqm : Reaches U q m :=
    reaches_own_of_round_le hqid hm hvc ham (by omega)
  obtain ⟨s', hds', hstq⟩ := stance_at_of_frozen hfd hm hqid hcm hrqm hmk
  have hss : s' = Stance.ack tx := Option.some.inj (hds' ▸ hds)
  subst hss
  have hackq : StanceIs U v (T.input tx) q (some (Stance.ack tx')) := by
    have h := hfv.2.2
    rw [← hconf.2] at h
    exact h
  have := stanceIs_unique (ham ▸ hstq) hackq
  simp only [Option.some.injEq, Stance.ack.injEq] at this
  exact hconf.1 this

/-- An eligible transaction's frozen supporters exclude a full unlock
certificate for the object, at any round: before the resolution the `⊥`
core would persist into the markers, after it the markers persist into
the votes. -/
theorem no_unlock_of_eligible (hmove : MoveDiscipline U)
    (hfd : FreezeDiscipline U) {aₖ a : BlockId} {o : Obj} {tx : Tx} (ha : a ∈ U.ids)
    (helig : EligibleFive U aₖ a o tx) : ∀ C' ∈ U.ids, ¬ IsFullUnlockCert U C' o := by
  intro C' hC' hunlock
  obtain ⟨-, w, hw, hwcard⟩ := helig
  have hn := F.card_validators
  obtain ⟨S, hS, hk, hall, hex⟩ := correct_core_exists hC' hunlock
  have hρ : 0 < (U.block C').round := round_pos_of_atLeast hC' quorum_pos hunlock
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  have hpersist : ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).author = v →
      (U.block C').round ≤ (U.block b).round + 1 →
      StanceIs U v o b (some Stance.bot) := by
    intro v hv b hb hab hr
    refine stance_persists (ρ₀ := (U.block C').round - 1) hmove hS hcount
      (fun x hx e he hae hre => ?_) hv hb hab (by omega)
    exact hae ▸ hall x hx e he hae (by omega)
  refine not_atLeastV_of_disjoint hcount (fun v hP hvS => ?_) ⟨w, hw, hwcard⟩
  obtain ⟨hfr, hst⟩ := hP
  have hvc : v ∈ (Correct : Finset Validator) := hS hvS
  obtain ⟨m, hm, ham, hrm, hmk⟩ := hfr
  have hcm : (U.block m).author ∈ (Correct : Finset Validator) := ham.symm ▸ hvc
  obtain ⟨s, hds, hsta⟩ := stance_at_of_frozen hfd hm ha hcm hrm hmk
  have hs : s = Stance.ack tx := Option.some.inj (stanceIs_unique (ham ▸ hsta) hst)
  subst hs
  rcases le_or_gt (U.block C').round ((U.block m).round + 1) with hcase | hcase
  · -- the ⊥ core persists into the marker, which declares an ACK
    have hbot := hpersist v hvS m hm ham hcase
    have hself : StanceIs U v o m (some (Stance.ack tx)) :=
      ham ▸ stanceIs_self_of_declares hm hds
    have := stanceIs_unique hbot hself
    simp at this
  · -- the marker precedes the core's votes, which then read the ACK
    obtain ⟨q, hq, haq, hqr, hPq⟩ := hex v hvS
    have hcq : (U.block q).author ∈ (Correct : Finset Validator) := haq.symm ▸ hvc
    have hrqm : Reaches U q m :=
      reaches_own_of_round_le hq hm hcq (ham.trans haq.symm) (by omega)
    obtain ⟨s', hds', hstq⟩ := stance_at_of_frozen hfd hm hq hcm hrqm hmk
    have hss : s' = Stance.ack tx := Option.some.inj (hds' ▸ hds)
    subst hss
    have hbotq : StanceIs U (U.block m).author o q (some Stance.bot) := by
      have := hPq
      rw [haq, ← ham] at this
      exact this
    have := stanceIs_unique hstq hbotq
    simp at this

theorem unlockEmptiesElection (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U) :
    UnlockEmptiesElection U := by
  intro o aₖ a ha ⟨C, hC, hunlock⟩ tx helig
  exact no_unlock_of_eligible hmove hfd ha helig C hC hunlock

/-- The reflection claim re-packaged at a resolution — the shape RS8
consumes: the resolving anchor's marker quorum is extracted from
`ResolvesFiveAt`'s third clause. -/
theorem recoveryReflects_at {A : Anchors U} (hmove : MoveDiscipline U)
    (hfd : FreezeDiscipline U) (hfive : Five Validator) {o : Obj} {i j : ℕ}
    {aₖ a : BlockId} {tx : Tx} (hres : ResolvesFiveAt U A o i j)
    (hlk : A.seq[i]? = some aₖ) (hla : A.seq[j]? = some a)
    (hin : T.input tx = o)
    (hcert : ∃ C ∈ U.ids, IsFullCert U C tx) :
    EligibleFive U aₖ a o tx ∧ ∀ tx', EligibleFive U aₖ a o tx' → tx' = tx := by
  obtain ⟨aₖ', a', hlk', hla', hq⟩ := hres.2.2.1
  rw [hlk] at hlk'
  rw [hla] at hla'
  rw [← Option.some.inj hlk', ← Option.some.inj hla'] at hq
  exact recoveryReflects hmove hfd hfive o aₖ a tx (anchor_mem hla) hq hin hcert

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ U
  exact ⟨fun A prio hord => resolutionUnique hord,
    fun hfd => ⟨recoverySafetyWin hfd,
      fun hmove => ⟨unlockEmptiesElection hmove hfd,
        fun hfive => ⟨recoveryReflects hmove hfd hfive,
          recoverySafetyBot hmove hfd hfive⟩⟩⟩⟩

end RecoverySafety

end RedSnapper

end LeanDag
