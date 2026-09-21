import LeanDag.RedSnapper.Five.CoinSuccess.Statement
import LeanDag.RedSnapper.Helpers.Coin
import LeanDag.RedSnapper.Helpers.Liveness

/-!
# Coin success — proof

Generated proof layer; not part of the audit surface. The engine is
`next_round_stance`: at round `ρ + 1` every correct block stands at the
target's value — a holder keeps or re-adopts it, and anyone else sees,
among its synchronised parents, `half` blocks standing elsewhere (the
concentrated holder set, or — under `Five` — the complement of its own
value's holders), which is the refutation the coin rule's adopt clauses
consume; the target's own value is read through its referenced
round-`ρ` block. Round `ρ + 2` then counts a correct quorum of
same-stance parents (`atLeast_of_witness`). Measurability is the
`AgreeUpto` transfer of stance reads.
-/

namespace LeanDag

namespace RedSnapper

namespace CoinSuccess

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

omit T in
/-- A correct validator's stance at its round-`ρ` block is its stance at
every round-`ρ` block. -/
private theorem holdsAt_of_block {v : Validator} {o : Obj} {ρ : ℕ} {q : BlockId}
    {y : Stance Tx} (hvc : v ∈ (Correct : Finset Validator)) (hq : q ∈ U.ids)
    (haq : (U.block q).author = v) (hrq : (U.block q).round = ρ)
    (hy : StanceIs U v o q (some y)) : HoldsAt U v o ρ y := by
  intro b hb hab hrb
  have hbq : b = q := U.no_equivocation b hb q hq (hab.symm ▸ hvc)
    (by rw [hab, haq]) (by rw [hrb, hrq])
  subst hbq
  exact hy

/-- The engine: every correct round-`(ρ + 1)` block stands at the
target's value. `hmov` supplies, for any correct holder of a different
value, `half` correct validators holding something other than it. -/
private theorem next_round_stance {w : Validator} {o : Obj} {ρ : ℕ} {x : Stance Tx}
    (hfd : FreezeDiscipline U) (hcr : CoinRule U w o ρ)
    (hpop0 : PopulatedOn U (Correct : Finset Validator) ρ)
    (hsync : SynchronisedOn U (Correct : Finset Validator) ρ)
    (hstanced : StancedAt U o ρ)
    (hwc : w ∈ (Correct : Finset Validator)) (hwx : HoldsAt U w o ρ x)
    (hmov : ∀ v ∈ (Correct : Finset Validator), ∀ y : Stance Tx, HoldsAt U v o ρ y →
      y ≠ x → ∃ D : Finset Validator, D ⊆ (Correct : Finset Validator) ∧
        half Validator ≤ D.card ∧ ∀ u ∈ D, ∃ z, z ≠ y ∧ HoldsAt U u o ρ z) :
    ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
      (U.block b).round = ρ + 1 → StanceIs U (U.block b).author o b (some x) := by
  intro b hb hc hr
  classical
  -- the self-parent, carrying the author's round-ρ stance
  obtain ⟨p, hpmem, hap⟩ := U.self_parent b hb hc (by omega)
  have hpid : p ∈ U.ids := U.complete b hb p hpmem
  have hpr : (U.block p).round = ρ := by
    have := round_of_mem_parents hb hpmem
    omega
  obtain ⟨y, hy⟩ := hstanced p hpid (hap ▸ hc) hpr
  have hyp : StanceIs U (U.block b).author o p (some y) := hap ▸ hy
  have hholds : HoldsAt U (U.block b).author o ρ y :=
    holdsAt_of_block hc hpid hap hpr hyp
  -- the target's round-ρ block, referenced by b
  obtain ⟨qw, hqw, haw, hrw⟩ := hpop0 w hwc
  have hqwpar : qw ∈ (U.block b).parents :=
    hsync b hb hc (by omega) qw hqw (haw.symm ▸ hwc) (by omega)
  have hwqw : StanceIs U w o qw (some x) := hwx qw hqw haw hrw
  have hwqw' : StanceIs U w o qw (some x) := hwqw
  -- adopting the target's value once a refutation is in hand
  have hadopt : IsRefutation U b o y → StanceIs U (U.block b).author o b (some x) := by
    intro href
    cases x with
    | ack tx =>
        have hcand : IsCandidate U b o tx := by
          have h₁ := candidate_of_stance_ack hfd hwc hwqw
          exact ⟨h₁.1, h₁.2.1, includes_mono (Reaches.single hqwpar) h₁.2.2⟩
        exact hcr.adopt_ack b hb hc hr p hpmem hap y hyp href qw hqwpar haw tx hwqw hcand
    | bot =>
        exact hcr.adopt_bot b hb hc hr p hpmem hap y hyp href qw hqwpar haw hwqw
  by_cases hyx : y = x
  · subst hyx
    by_cases href : IsRefutation U b o y
    · exact hadopt href
    · exact hcr.keep b hb hc hr p hpmem hap y hyp href
  · -- a holder of a different value is refuted by the `half` others
    obtain ⟨D, hDc, hDcard, hDz⟩ := hmov (U.block b).author hc y hholds hyx
    refine hadopt (atLeast_of_witness hDcard ?_)
    intro u hu
    obtain ⟨z, hz, huz⟩ := hDz u hu
    obtain ⟨qu, hqu, hau, hru⟩ := hpop0 u (hDc hu)
    refine ⟨qu, hsync b hb hc (by omega) qu hqu (hau.symm ▸ hDc hu) (by omega), hau, ?_⟩
    exact ⟨z, hau.symm ▸ huz qu hqu hau hru, hz⟩

/-- Round `ρ + 2`: a correct quorum of same-stance parents makes the
certificate. -/
private theorem certified {w : Validator} {o : Obj} {ρ : ℕ} {x : Stance Tx}
    (hfd : FreezeDiscipline U)
    (hpop1 : PopulatedOn U (Correct : Finset Validator) (ρ + 1))
    (hsync : SynchronisedOn U (Correct : Finset Validator) ρ)
    (hnext : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
      (U.block b).round = ρ + 1 → StanceIs U (U.block b).author o b (some x)) :
    CertifiedAt U o x (ρ + 2) := by
  have _ := w
  intro C hC hcor hrC
  have hwit : ∀ (P : BlockId → Prop),
      (∀ q ∈ U.ids, (U.block q).author ∈ (Correct : Finset Validator) →
        (U.block q).round = ρ + 1 → P q) →
      AtLeast U (quorum Validator) (U.block C).parents P := by
    intro P hP
    refine atLeast_of_witness quorum_le_card_correct ?_
    intro v hv
    obtain ⟨q, hq, haq, hrq⟩ := hpop1 v hv
    refine ⟨q, hsync C hC hcor (by omega) q hq (haq.symm ▸ hv) (by omega), haq,
      hP q hq (haq.symm ▸ hv) hrq⟩
  cases x with
  | ack tx =>
      refine Or.inl ⟨tx, rfl, ?_⟩
      refine hwit (fun q => IsFastVote U q tx) ?_
      intro q hq hqc hqr
      have hst := hnext q hq hqc hqr
      have hcand := candidate_of_stance_ack hfd hqc hst
      exact ⟨hcand.1, hcand.2.2, hcand.2.1 ▸ hst⟩
  | bot =>
      refine Or.inr ⟨rfl, ?_⟩
      exact hwit (fun q => StanceIs U (U.block q).author o q (some Stance.bot))
        (fun q hq hqc hqr => hnext q hq hqc hqr)

theorem coinConcentrated : CoinConcentrated U := by
  intro w o ρ x H hfd hcr hpop0 hpop1 hsync hstanced hHc hHcard hHx hwH
  refine certified (w := w) hfd hpop1 hsync
    (next_round_stance hfd hcr hpop0 hsync hstanced (hHc hwH) (hHx w hwH) ?_)
  intro v hv y hy hne
  exact ⟨H, hHc, hHcard, fun u hu => ⟨x, fun h => hne h.symm, hHx u hu⟩⟩

theorem coinFragmented (hfive : Five Validator) : CoinFragmented U := by
  intro w o ρ hfd hcr hpop0 hpop1 hsync hstanced hnoconc hwc
  classical
  have hval : ∀ v ∈ (Correct : Finset Validator), ∃ y : Stance Tx, HoldsAt U v o ρ y := by
    intro v hv
    obtain ⟨q, hq, haq, hrq⟩ := hpop0 v hv
    obtain ⟨y, hy⟩ := hstanced q hq (haq.symm ▸ hv) hrq
    exact ⟨y, holdsAt_of_block hv hq haq hrq (haq ▸ hy)⟩
  haveI : Inhabited (Stance Tx) := ⟨Stance.bot⟩
  choose! stance hstance using hval
  have hmov : ∀ v ∈ (Correct : Finset Validator), ∀ y : Stance Tx, HoldsAt U v o ρ y →
      y ≠ stance w → ∃ D : Finset Validator, D ⊆ (Correct : Finset Validator) ∧
        half Validator ≤ D.card ∧ ∀ u ∈ D, ∃ z, z ≠ y ∧ HoldsAt U u o ρ z := by
    intro v hv y hy hne
    refine ⟨(Correct : Finset Validator).filter (fun u => ¬ stance u = y),
      Finset.filter_subset _ _, ?_, ?_⟩
    · -- the holders of y are below half, so their complement fills it
      have hholders : ((Correct : Finset Validator).filter
          (fun u => stance u = y)).card + 1 ≤ half Validator := by
        by_contra hbig
        refine hnoconc y ⟨(Correct : Finset Validator).filter (fun u => stance u = y),
          Finset.filter_subset _ _, by omega, ?_⟩
        intro u hu
        obtain ⟨huc, hus⟩ := Finset.mem_filter.mp hu
        exact hus ▸ hstance u huc
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Correct : Finset Validator)) (p := fun u => stance u = y)
      have hcorr : Fintype.card Validator ≤
          (Correct : Finset Validator).card + F.f := by
        have h1 : ((Correct : Finset Validator))ᶜ.card ≤ F.f := by
          have : ((Correct : Finset Validator))ᶜ = F.byzantine := by
            simp [Correct]
          rw [this]
          exact F.card_byzantine
        have h2 := Finset.card_compl (Correct : Finset Validator)
        omega
      have h5 := hfive.card_validators
      have hh : half Validator = 2 * F.f + 1 := rfl
      omega
    · intro u hu
      obtain ⟨huc, hus⟩ := Finset.mem_filter.mp hu
      exact ⟨stance u, hus, hstance u huc⟩
  exact ⟨stance w, hstance w hwc,
    certified (w := w) hfd hpop1 hsync
      (next_round_stance hfd hcr hpop0 hsync hstanced hwc (hstance w hwc) hmov)⟩

theorem coinSuccessCount (hfive : Five Validator) : CoinSuccessCount U := by
  intro o ρ hfd hpop0 hpop1 hsync hstanced
  classical
  by_cases hconc : ∃ (x : Stance Tx) (H : Finset Validator),
      H ⊆ (Correct : Finset Validator) ∧ half Validator ≤ H.card ∧
        ∀ v ∈ H, HoldsAt U v o ρ x
  · obtain ⟨x, H, hHc, hcard, hHx⟩ := hconc
    exact ⟨H, hcard, fun w hw hcr => ⟨x, coinConcentrated w o ρ x H hfd hcr
      hpop0 hpop1 hsync hstanced hHc hcard hHx hw⟩⟩
  · refine ⟨(Correct : Finset Validator), half_le_card_correct, fun w hw hcr => ?_⟩
    obtain ⟨x, -, hcert⟩ := coinFragmented hfive w o ρ hfd hcr hpop0 hpop1 hsync
      hstanced (fun x hx => hconc ⟨x, hx⟩) hw
    exact ⟨x, hcert⟩

omit T in
/-- One direction of the `HoldsAt` transfer. -/
private theorem holdsAt_mp {U₁ U₂ : Universe Validator BlockId Tx Obj} {ρ : ℕ} {o : Obj}
    (h : AgreeUpto U₁ U₂ ρ) {v : Validator} {x : Stance Tx}
    (h1 : HoldsAt U₁ v o ρ x) : HoldsAt U₂ v o ρ x := by
  intro b hb hab hrb
  obtain ⟨hb₁, hrb₁⟩ := (h.ids b).mpr ⟨hb, le_of_eq hrb⟩
  have hblk := h.block b hb₁ hrb₁
  have hst := h1 b hb₁ (by rw [hblk]; exact hab) (by rw [hblk]; exact hrb)
  exact (h.stanceIs_iff hb₁ hrb₁).mp hst

omit T in
theorem coinMeasurable : CoinMeasurable Validator BlockId Tx Obj := by
  intro U₁ U₂ ρ o h
  refine ⟨fun v x => ⟨holdsAt_mp h, holdsAt_mp h.symm⟩, ?_, ?_⟩
  · intro h1 b hb hc hrb
    obtain ⟨hb₁, hrb₁⟩ := (h.ids b).mpr ⟨hb, le_of_eq hrb⟩
    have hblk := h.block b hb₁ hrb₁
    obtain ⟨s, hs⟩ := h1 b hb₁ (by rw [hblk]; exact hc) (by rw [hblk]; exact hrb)
    exact ⟨s, hblk ▸ (h.stanceIs_iff hb₁ hrb₁).mp hs⟩
  · intro h2 b hb hc hrb
    obtain ⟨hb₂, hrb₂⟩ := (h.symm.ids b).mpr ⟨hb, le_of_eq hrb⟩
    have hblk := h.symm.block b hb₂ hrb₂
    obtain ⟨s, hs⟩ := h2 b hb₂ (by rw [hblk]; exact hc) (by rw [hblk]; exact hrb)
    exact ⟨s, hblk ▸ (h.symm.stanceIs_iff hb₂ hrb₂).mp hs⟩

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _
  exact ⟨fun U => ⟨coinConcentrated, fun hfive =>
    ⟨coinFragmented hfive, coinSuccessCount hfive⟩⟩, coinMeasurable⟩

end CoinSuccess

end RedSnapper

end LeanDag
