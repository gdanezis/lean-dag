import LeanDag.Adaptive.Liveness
import LeanDag.Adaptive.Growth
import LeanDag.Mysticeti.Properties
/-!
# Adaptive Mysticeti: the core as an instance

The generic adaptive mechanism (`Adaptive/{Policy,Run,Liveness}.lean`)
at `MysticetiProperties.mysticetiRule`, with the core's proofs of its
five properties. The generic theorems ask for the precondition `Live`
stage by stage, and it is read here at `coreSupport.live` — the socket
both execution models reach, coverage through `Timed.live_of_coverage`
and the reactive discipline through `coreSupport_live_of_reactiveLive`.
Nothing below names synchrony.
-/

namespace LeanDag

open Properties MysticetiProperties

/-- The adaptive policy over the core's carrier. -/
abbrev AdaptivePolicy (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    [Slots Validator] : Type :=
  Adaptive.Policy (mysticetiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

namespace AdaptivePolicy

/-- The constant policy: reassign nothing. -/
def const (W : ℕ) (hW : 0 < W) (hinj : Function.Injective S.slotRound) :
    AdaptivePolicy Validator BlockId Payload :=
  Adaptive.Policy.const W hW hinj

@[simp] theorem const_pick (W : ℕ) (hW : 0 < W)
    (hinj : Function.Injective S.slotRound)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (v : ℕ → Option BlockId) (k : ℕ) : (const W hW hinj).pick U V v k = S.leader k := rfl

end AdaptivePolicy

/-! ## Congruence, at induced schedules -/

/-- Only the leader clause of `IsLeaderBlock` consults the assignment,
at the slot itself. -/
theorem isLeaderBlock_slotsOf_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {k : ℕ} {L : BlockId} (hk : a₁ k = a₂ k)
    (h : IsLeaderBlock (S := slotsOf hinj a₁) U k L) :
    IsLeaderBlock (S := slotsOf hinj a₂) U k L :=
  isLeaderBlock_congr (S₁ := slotsOf hinj a₁) (S₂ := slotsOf hinj a₂) rfl hk h

/-- **Congruence below the bound**: two assignments agreeing below `B`
derive the same bounded verdicts. -/
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    DecidedWithin (S := slotsOf hinj a₂) U V B k v :=
  AnchoredRule.decidedWithin_slotsOf_congr coreLaws trivial ha h

/-! ## Runs -/

/-- A run closed up to epoch height `E`, over the core. -/
abbrev PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) : Type :=
  Adaptive.PartialRun (R := mysticetiRule) P U V E

/-- A total run: the adaptive fixpoint itself, over the core. -/
abbrev AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : Type :=
  Adaptive.Run (R := mysticetiRule) P U V

/-- A total run is partial at every height. -/
def AdaptiveRun.toPartial {P : AdaptivePolicy Validator BlockId Payload}
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V) (E : ℕ) :
    PartialRun P U V E :=
  Adaptive.Run.toPartial R E

/-- **The master agreement lemma**, for the core. -/
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k :=
  Adaptive.partialRun_agree agree R₁ R₂

/-- Assignments agree wherever the common verdicts determine them. -/
theorem partialRun_assign_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ m, epochOf P.W m < min E₁ E₂ + 1 → R₁.assign m = R₂.assign m :=
  Adaptive.partialRun_assign_agree agree R₁ R₂

/-- **AL3 — safety: the adaptive fixpoint is unique.** -/
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    (∀ k, R₁.vdct k = R₂.vdct k) ∧ (∀ m, R₁.assign m = R₂.assign m) :=
  Adaptive.run_agree agree R₁ R₂

/-- The verdict form of uniqueness, in the shape of M6. -/
theorem adaptive_decided_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) (k : ℕ) :
    R₁.vdct k = R₂.vdct k :=
  (adaptiveRun_agree R₁ R₂).1 k

/-- **The adaptive ledger is agreed** — M7's shape. -/
theorem adaptive_commitSeq_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) (n : ℕ) :
    commitSeq R₁.vdct n = commitSeq R₂.vdct n := by
  rw [funext (adaptiveRun_agree R₁ R₂).1]

/-- **Conservativity.** Under the constant policy a run's verdicts are
ordinary `Decided` verdicts of the base schedule. -/
theorem AdaptivePolicy.const_run_decided {W : ℕ} {hW : 0 < W}
    {hinj : Function.Injective S.slotRound}
    {V : View Validator BlockId Payload U}
    (R : AdaptiveRun (AdaptivePolicy.const (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) W hW hinj) U V) (k : ℕ) :
    Decided U V k (R.vdct k) :=
  Adaptive.Policy.const_run_decided R k

/-! ## Liveness -/

/-- **The adaptive fairness clause**, for the core. -/
abbrev PlacesRuns (P : AdaptivePolicy Validator BlockId Payload)
    (T : Finset Validator) (c : ℕ) : Prop :=
  Adaptive.PlacesRuns P T c

section Existence

variable {P : AdaptivePolicy Validator BlockId Payload}
variable {T : Finset Validator} {c : ℕ}

/-- **The core's staged precondition**, at the support both execution
models reach: `Timed.live_of_coverage` supplies it under coverage,
`coreSupport_live_of_reactiveLive` under the reactive discipline. -/
abbrev coreSupportLive (S : Slots Validator)
    {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  (coreSupport (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).live
    (coreReliability Validator) S (U := U) V T lo K

/-- **One epoch closes**, from the staged precondition alone. -/
theorem epoch_closes (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U) (v : ℕ → Option BlockId) (E : ℕ)
    (hlive : coreSupportLive (slotsOf P.inj (fun m => P.pick U V v m)) V T P.W
      (P.W * (E + 2))) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedBelow mysticetiRule (slotsOf P.inj (fun m => P.pick U V v m))
        (P.W * (E + 2)) V k w :=
  Adaptive.epoch_closes_of_support coreSupport_commits indirect hc hspans V v E hruns hlive

/-- **Partial runs exist at every height** — the finite-horizon form. -/
theorem exists_partialRun (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U) (E : ℕ)
    (hlive : ∀ (E' : ℕ), E' < E → ∀ (A : PartialRun P U V E'),
      coreSupportLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W
        (P.W * (E' + 2))) :
    Nonempty (PartialRun P U V E) :=
  Adaptive.exists_partialRun_of_support coreSupport_commits indirect hc hspans hruns V E hlive

/-- **AL5: the adaptive fixpoint exists**, under a policy that places
runs, with the precondition holding at every height. -/
theorem adaptiveRun_exists (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U)
    (hlive : ∀ (E : ℕ) (A : PartialRun P U V E),
      coreSupportLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W
        (P.W * (E + 2))) :
    Nonempty (AdaptiveRun P U V) :=
  Adaptive.run_exists_of_support agree coreSupport_commits indirect hc hspans hruns V hlive

/-- **Every reliable-led slot past the first epoch commits**, in every
run. -/
theorem adaptiveRun_commits {V : View Validator BlockId Payload U}
    (A : AdaptiveRun P U V) {k : ℕ} (hk : P.W ≤ k) (hK : k < P.W * (epochOf P.W k + 2))
    (hlive : coreSupportLive (slotsOf P.inj A.assign) V T P.W
      (P.W * (epochOf P.W k + 2)))
    (hlead : A.assign k ∈ T) :
    ∃ L, A.vdct k = some L :=
  Adaptive.Run.commits_of_support agree coreSupport_commits A hlive hk hK hlead

/-- **Every epoch past the first carries `c` consecutive commits**, in
every run. -/
theorem adaptiveRun_commits_in_epoch (hruns : PlacesRuns P T c)
    {V : View Validator BlockId Payload U} (A : AdaptiveRun P U V) (e : ℕ)
    (hlive : coreSupportLive (slotsOf P.inj A.assign) V T P.W (P.W * (e + 2))) :
    ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → ∃ L, A.vdct (b + i) = some L :=
  Adaptive.Run.commits_in_epoch_of_support agree coreSupport_commits hruns A e hlive

end Existence

/-! ## Growth, for the core -/

/-- The constant policy is stable under extension. -/
theorem AdaptivePolicy.const_stable (W : ℕ) (hW : 0 < W)
    (hinj : Function.Injective S.slotRound) :
    (AdaptivePolicy.const (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
      W hW hinj).Stable :=
  Adaptive.Policy.const_stable W hW hinj

/-- **The adaptive fixpoint is a prefix of the fixpoint on any
extension**, under the core's persistence condition `Quorate` at the
smaller run's schedule and a stable policy. -/
theorem adaptiveRun_agree_extends {P : AdaptivePolicy Validator BlockId Payload}
    {U' : BlockUniverse Validator BlockId Payload}
    (hext : Extends (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U U')
    {V : View Validator BlockId Payload U} {V' : View Validator BlockId Payload U'}
    (hsub : V.ids ⊆ V'.ids) (hst : P.Stable)
    (R₁ : AdaptiveRun P U V) (R₂ : AdaptiveRun P U' V') :
    (∀ k, R₁.vdct k = R₂.vdct k) ∧ (∀ m, R₁.assign m = R₂.assign m) :=
  Adaptive.run_agree_extends agree persist hst hext hsub R₁ R₂

end LeanDag
