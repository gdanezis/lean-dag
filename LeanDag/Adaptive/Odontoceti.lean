import LeanDag.Adaptive.Liveness
import LeanDag.Adaptive.Growth
import LeanDag.Odontoceti.Properties
/-!
# Adaptive leaders under the two-round rule

The generic adaptive mechanism at `odontocetiRule`: its `Agree`, its
`LeaderCommits` read off the vote support through the timed bridge, and
its `Descends`. The precondition asks the view to cover one round past
a slot, where the core asks two.
-/

namespace LeanDag

namespace Odontoceti

open Properties OdontocetiProperties

/-- The adaptive policy over Odontoceti's carrier. -/
abbrev AdaptivePolicy (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] (BlockId : Type) [LinearOrder BlockId] (Payload : Type)
    [Slots Validator] : Type :=
  Adaptive.Policy (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- A run closed up to epoch height `E`, two-round rule. -/
abbrev PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) : Type :=
  Adaptive.PartialRun (R := odontocetiRule) P U V E

/-- A total run: the adaptive fixpoint, two-round rule. -/
abbrev AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : Type :=
  Adaptive.Run (R := odontocetiRule) P U V

/-- **The master agreement lemma, two-round rule.** -/
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k :=
  Adaptive.partialRun_agree agree R₁ R₂

/-- **Safety, two-round rule: the adaptive fixpoint is unique**, with no
fairness, synchrony or view hypothesis. -/
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    (∀ k, R₁.vdct k = R₂.vdct k) ∧ (∀ m, R₁.assign m = R₂.assign m) :=
  Adaptive.run_agree agree R₁ R₂

section Existence

variable {P : AdaptivePolicy Validator BlockId Payload}
variable {T : Finset Validator} {c R N : ℕ}

/-- **Odontoceti's precondition, staged**: the vote support's, at the
core's fault model. -/
abbrev odoLive (S : Slots Validator) {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  (voteSupport (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload))).live (coreReliability Validator) S V T lo K

/-- **A reliably-led slot commits**, from the vote support's Law 3. -/
theorem leaderCommits :
    LeaderCommits (odontocetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (fun S {U} V T lo K => odoLive S (U := U) V T lo K) :=
  (voteSupport (odontocetiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload))).leaderCommits voteSupport_commits

/-- The precondition, from the global hypotheses: synchrony from `R`,
population to a horizon the view covers, one round past every slot of
the window. -/
theorem odoLive_of {S : Slots Validator} {V : View Validator BlockId Payload U} {lo K : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound lo)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hcov : V.CoversUpto N)
    (hN : ∀ k, k < K → S.slotRound k + 1 ≤ N) : odoLive S V T lo K :=
  Timed.live_of_coverage (voteSupport (odontocetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))) (Timed.voteSupport_ofCoverage _)
    ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩
    hs hpop S V hcov hRW hN

/-- **Partial runs exist at every height, two-round rule**, from the
staged precondition alone. `odoLive_of` supplies it under coverage. -/
theorem exists_partialRun (hc : 0 < c) (hruns : Adaptive.PlacesRuns P T c)
    (hspans : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U) (E : ℕ)
    (hlive : ∀ (E' : ℕ), E' < E → ∀ (A : PartialRun P U V E'),
      odoLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E' + 2))) :
    Nonempty (PartialRun P U V E) :=
  Adaptive.exists_partialRun leaderCommits
    (Adaptive.descends_slotsOf indirect hc hspans P.inj) hruns V E hlive

/-- **AL7: adaptive Odontoceti is safe and live.** -/
theorem adaptiveRun_exists (hc : 0 < c) (hruns : Adaptive.PlacesRuns P T c)
    (hspans : (odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U)
    (hlive : ∀ (E : ℕ) (A : PartialRun P U V E),
      odoLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E + 2))) :
    Nonempty (AdaptiveRun P U V) :=
  Adaptive.run_exists agree leaderCommits
    (Adaptive.descends_slotsOf indirect hc hspans P.inj) hruns V hlive

end Existence

end Odontoceti

end LeanDag
