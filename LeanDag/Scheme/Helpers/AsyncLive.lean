import LeanDag.Scheme.Model.AsyncLive
import LeanDag.Scheme.Helpers.AsyncPace
import LeanDag.Scheme.Helpers.OneBuffer
import LeanDag.Steelhead.Helpers.Coin
/-!
# The asynchronous rows across waves

A coin per slot, drawn in `M` blocks of `d` consecutive slots from slot
`s₀` (`Steelhead.coinOfBlocksFrom`). A block every coin of which names a
safe leader is a run of `d` slots that commit on every reliable
validator's own view, and a run of `d` slots that spans eligibility
decides every slot below it (`eventually_decided_of_good_block`). The slots
below `s₀` therefore stay undecided only if every block holds a coin
outside its slot's safe set, which Steelhead's block count bounds by
`badBlockBoundAt c d ^ M` at a floor `c` (`undecided_le`); the bound
vanishes as `M` grows (`badBlockBound_tendsto_zero`).
-/

namespace LeanDag

namespace Scheme

open Filter Topology
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable [P.Mechanised] {q : ℕ} [P.Quorate q] {p : Params}
variable {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator} {N qp : ℕ}

/-- **A block of safe coins decides every slot below the blocks**, on every
reliable validator's own view from some time on. -/
theorem eventually_decided_of_good_block (σ : VoteSel Validator BlockId Payload P honest)
    (ap : AsyncPace qp U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    {s₀ d M : ℕ} (dflt : Validator) (g : Fin M → Fin d → Validator) (hc : p.CertFits q)
    (hcm : p.commitThreshold ≤ T.card) (hq : qp ≤ T.card) (hd : 0 < d)
    (hspan : (schemeAnchored p σ).SpansEligible (S := S₀) d)
    (hN : S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N) (j : Fin M)
    (hgood : ∀ i : Fin d, g j i ∈ safeAt p U (S₀.slotRound (s₀ + j * d + i))) :
    ap.Eventually fun V => ∀ s < s₀, ∃ v,
      (schemeAnchored p σ).Decided (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
        U V s v := by
  letI S' := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt)
  obtain ⟨t, ht⟩ := ap.delivered
  refine ⟨t, fun t' htt' v hv s hs => ?_⟩
  have hjM := j.isLt
  refine AnchoredRule.decided_below_of_run (S := S')
    (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h) hd hspan
    (b := s₀ + j * d) (Led := fun s => S'.leader s ∈ safe p U s) (fun i hi => ?_)
    (fun j' _ h2 hj' => ?_) s (by omega)
  · change Steelhead.coinOfBlocksFrom s₀ g dflt (s₀ + j * d + i) ∈
      safeAt p U (S₀.slotRound (s₀ + j * d + i))
    have := Steelhead.coinOfBlocksFrom_read (b := s₀) hd g dflt j ⟨i, hi⟩
    rw [this]; exact hgood ⟨i, hi⟩
  · have hle : j' ≤ s₀ + M * d := by
      have : (j : ℕ) * d + d ≤ M * d := by
        have := Nat.mul_le_mul_right d (show (j : ℕ) + 1 ≤ M by omega)
        rw [Nat.add_mul, one_mul] at this; exact this
      omega
    have hmono := S₀.mono hle
    obtain ⟨L, -, hL⟩ := decided_of_safe_of_holds (S := S') σ hc.1 hc.2 hcm
      (ap.populated hq _ (by change S₀.slotRound j' + _ ≤ N; omega)) hj'
      (V := ap.viewAt hv t') fun b hb hbT => ht t' htt' v hv b hb hbT
    exact ⟨L, hL⟩

/-- **The slots below the blocks stay undecided** with probability at most
`badBlockBoundAt c d ^ M`, at a floor `c` on the safe sets of the blocks'
slots. -/
theorem undecided_le [Nonempty Validator] (σ : VoteSel Validator BlockId Payload P honest)
    (ap : AsyncPace qp U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    (dflt : Validator) {s₀ d M c : ℕ} (hc : p.CertFits q) (hcm : p.commitThreshold ≤ T.card)
    (hq : qp ≤ T.card) (hd : 0 < d) (hspan : (schemeAnchored p σ).SpansEligible (S := S₀) d)
    (hN : S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N)
    (hfloor : ∀ s, s₀ ≤ s → s < s₀ + M * d → c ≤ (safeAt p U (S₀.slotRound s)).card) :
    (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
        (ap.UndecidedBelow p σ S₀ hS dflt s₀ M d) ≤
      Steelhead.Coin.badBlockBoundAt Validator c d ^ M := by
  letI : Faults Validator := noFaults
  set G : Fin M → Fin d → Finset Validator :=
    fun j i => safeAt p U (S₀.slotRound (s₀ + j * d + i))
  have hG : ∀ j i, c ≤ (G j i).card := fun j i => by
    have hj := j.isLt
    have hi := i.isLt
    have : (j : ℕ) * d + i < M * d := by
      have := Nat.mul_le_mul_right d (show (j : ℕ) + 1 ≤ M by omega)
      rw [Nat.add_mul, one_mul] at this; omega
    exact hfloor _ (by omega) (by omega)
  have hsub : ap.UndecidedBelow p σ S₀ hS dflt s₀ M d ⊆
      {g | ∀ j ∈ (Finset.univ : Finset (Fin M)), ∃ i, g j i ∉ G j i} := by
    intro g hg j _
    by_contra hall
    push Not at hall
    exact hg (eventually_decided_of_good_block σ ap S₀ hS dflt g hc hcm hq hd hspan hN j hall)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have := Steelhead.no_good_block_prob_le (Finset.univ : Finset (Fin M)) G hG
  rwa [Finset.card_univ, Fintype.card_fin] at this

/-- **The floors at a row ready for the count**: one safe validator at one
buffer round, `q − f` at two, and a third of the validators at one buffer
round where `n ≥ 5f + 3c + 1` and `q = n − f − c`. -/
theorem floors {f b r : ℕ} (ap : AsyncPace q U T N) (hf : honestᶜ.card ≤ f)
    (hp : p.AsyncReady (Fintype.card Validator) f q b) (hq : q ≤ T.card)
    (hr : r + p.voteOffset ≤ N) :
    (1 ≤ b → 1 ≤ (safeAt p U r).card) ∧ (2 ≤ b → q - f ≤ (safeAt p U r).card) ∧
      (1 ≤ b → T ⊆ honest → ∀ c, 5 * f + 3 * c + 1 ≤ Fintype.card Validator →
        q + f + c = Fintype.card Validator → (Fintype.card Validator + 2) / 3 ≤
          (safeAt p U r).card) := by
  obtain ⟨hq2, hvo, -, -⟩ := hp
  have hT : T.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (Validity.Quorate.pos P) hq)
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb hTh c hn hqn => ?_⟩
  · exact Finset.card_pos.mpr
      (safeAt_nonempty hf hq2 (by omega) hT (ap.populated hq (r + 2) (by omega)))
  · have := le_card_safeAt (p := p) hf hq2 (by omega) hT (ap.populated hq (r + 3) (by omega))
    omega
  · have := card_safeAt_third (p := p) hf (by omega) hTh (ap.populated hq (r + 1) (by omega))
      hq hn hqn
    omega

/-- **The bound vanishes** at a positive floor. -/
theorem badBlockBound_tendsto_zero [Nonempty Validator] {c d : ℕ} (hc : 0 < c) :
    Tendsto (fun M : ℕ => Steelhead.Coin.badBlockBoundAt Validator c d ^ M) atTop (𝓝 0) := by
  refine ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ?_
  unfold Steelhead.Coin.badBlockBoundAt
  have hn := Fintype.card_pos (α := Validator)
  have hnd : (Fintype.card Validator : ℝ≥0∞) ^ d ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hn.ne')
  rw [ENNReal.div_lt_iff (Or.inl hnd) (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))),
    one_mul, ← Nat.cast_pow, Nat.cast_lt]
  have h1 : 1 ≤ c ^ d := Nat.one_le_pow _ _ hc
  have h2 : 1 ≤ Fintype.card Validator ^ d := Nat.one_le_pow _ _ hn
  omega

end Scheme

end LeanDag
