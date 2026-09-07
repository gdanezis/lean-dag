import LeanDag.Adaptive.Liveness
import LeanDag.Adaptive.Growth
import LeanDag.Mysticeti.Properties
/-!
# Adaptive Mysticeti: the core as an instance

The adaptive mechanism (`Adaptive/{Policy,Run,Liveness}.lean`) is stated
over a `Properties.BoundedRule` and five properties. This file applies
it to the core: every statement the arc made before the mechanism was
generic — `AdaptivePolicy`, `PartialRun`, `AdaptiveRun`,
`partialRun_agree`, `adaptiveRun_agree`, `epoch_closes`,
`exists_partialRun`, `adaptiveRun_exists`, and the congruence lemmas —
is restated here verbatim, and each is now a corollary of the generic
theorem at `MysticetiProperties.mysticetiRule` with the core's
proofs of the five properties. Nothing downstream changes.

The one visible difference is in how the liveness hypotheses are
supplied: the generic theorems ask for the protocol's precondition
`Live` stage by stage, and the core's `coreLive` reads no leader, so
the usual global hypotheses — `SynchronisedOn`, `PopulatedOn` to a
horizon, `CoversUpto` — produce it at every stage. That is what the
proofs below do and all they do.
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

/-- **Congruence below the bound.** Two assignments agreeing below `B`
derive the same bounded verdicts — `decidedWithin_congr_of_slotRound`
at two induced schedules. -/
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
variable {T : Finset Validator} {c R N : ℕ}

/-- **One epoch closes** — the generic `Adaptive.epoch_closes` with
`coreLive` assembled from the global hypotheses. -/
theorem epoch_closes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N)
    (v : ℕ → Option BlockId) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 2)) + 2 ≤ N) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedBelow mysticetiRule (slotsOf P.inj (fun m => P.pick U V v m))
        (P.W * (E + 2)) V k w := by
  have hlive : coreLive (slotsOf P.inj (fun m => P.pick U V v m)) V T P.W (P.W * (E + 2)) :=
    coreLive_of hcard hs hRW hpop hcov fun k hk => by
      have := S.mono (le_of_lt hk); change S.slotRound k + 2 ≤ N; omega
  intro k hk
  obtain ⟨w, hw⟩ := Adaptive.epoch_closes leaderCommits
    (Adaptive.descends_slotsOf indirect hc hspans P.inj) hruns V v E hlive k hk
  exact ⟨w, hw⟩

/-- **Partial runs exist at every height** — the finite-horizon form. -/
theorem exists_partialRun (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 1)) + 2 ≤ N) :
    Nonempty (PartialRun P U V E) :=
  Adaptive.exists_partialRun leaderCommits (Adaptive.descends_slotsOf indirect hc hspans P.inj)
    hruns V E (fun E' hE' _ => coreLive_of hcard hs hRW hpop hcov fun k hk => by
      have h1 : k ≤ P.W * (E + 1) := by
        have := Nat.mul_le_mul_left P.W (show E' + 2 ≤ E + 1 by omega)
        omega
      have := S.mono h1
      change S.slotRound k + 2 ≤ N
      omega)

/-- **AL5: the adaptive fixpoint exists.** On a DAG synchronised over a
quorum of reliable validators and populated at every round, under a
policy that places runs, a total adaptive run exists on every view
caught up to every horizon. With `adaptiveRun_agree` it is THE fixpoint:
adaptive Mysticeti decides every slot, and uniquely. -/
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r)
    (V : View Validator BlockId Payload U) (hcov : ∀ N, V.CoversUpto N) :
    Nonempty (AdaptiveRun P U V) :=
  Adaptive.run_exists agree leaderCommits (Adaptive.descends_slotsOf indirect hc hspans P.inj)
    hruns V (fun E _ => coreLive_of hcard hs hRW (fun r _ _ => PopulatedOn.mono hT (hpop r))
      (hcov _) fun k hk => by
        have := S.mono (le_of_lt hk)
        change S.slotRound k + 2 ≤ S.slotRound (P.W * (E + 2)) + 2
        omega)

/-! ## What the run commits, for the core -/

/-- **Every reliable-led slot past the first epoch commits**, in every
run, on a view caught up two rounds past it. -/
theorem adaptiveRun_commits (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    {V : View Validator BlockId Payload U} (hcov : V.CoversUpto N) (A : AdaptiveRun P U V)
    {k : ℕ} (hk : P.W ≤ k) (hN : S.slotRound k + 2 ≤ N) (hlead : A.assign k ∈ T) :
    ∃ L, A.vdct k = some L :=
  Adaptive.Run.commits agree leaderCommits A (lo := P.W) (K := k + 1)
    (coreLive_of (S := slotsOf P.inj A.assign) hcard hs hRW hpop hcov fun j hj => by
        have := S.mono (show j ≤ k by omega)
        change S.slotRound j + 2 ≤ N
        omega)
    hk (by omega) hlead

/-- **Every epoch past the first carries `c` consecutive commits**, in
every run — the liveness statement AL5 was standing in for. -/
theorem adaptiveRun_commits_in_epoch (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hruns : PlacesRuns P T c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r)
    {V : View Validator BlockId Payload U} (hcov : ∀ N, V.CoversUpto N)
    (A : AdaptiveRun P U V) (e : ℕ) :
    ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → ∃ L, A.vdct (b + i) = some L :=
  Adaptive.Run.commits_in_epoch agree leaderCommits hruns A e
    (coreLive_of (S := slotsOf P.inj A.assign) hcard hs hRW
      (fun r _ _ => PopulatedOn.mono hT (hpop r)) (hcov _) fun k hk => by
        have := S.mono (le_of_lt hk)
        change S.slotRound k + 2 ≤ S.slotRound (P.W * (e + 2)) + 2
        omega)

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
