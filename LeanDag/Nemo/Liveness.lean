import LeanDag.Nemo.Decision
import LeanDag.Mysticeti.Liveness
/-!
# Nemo-Nemo: crash liveness

The liveness chain for the crash arc, mirroring the hybrid arc's
structure at the majority quorum over the crash `Universe`. Crash
safety is free — everything through `Decision.lean` holds on any
committee — and only liveness pays: `CrashFaults` (`crashed.card ≤ f`,
`2f + 1 ≤ n`) is defined here and consumed through one bridge,
`majority_le_card_live`.

**No `directSkip`.** The implementation pins the direct-skip quorum to
the full stake, so a crashed leader's empty slot cannot be skipped at
its own round; every skip routes through `indirectSkip`, anchored on a
later live-led commit, which is why the headline is
`all_decided_below_of_fairRun` with no L5 analogue.

**Why a run of two consecutive commits.** A crashed validator is
indistinguishable from a slow one, so the anchor scan cannot step past
an undecided slot, and every commit at round `r` casts a shadow at
round `r − 1` — a slot it can neither anchor nor step past. A lone
commit settles only itself and round `r − 2`; two commits at
*consecutive* rounds are the minimal self-sufficient configuration,
since the upper one anchors the lower one's shadow and its own shadow
is the lower commit itself. Hence `FairRunOn T 2`, harmless for
round-robin over `n = 2f + 1`: `f + 1` live validators cannot be
pairwise non-adjacent on a cycle of `2f + 1`.

The participation vocabulary is restated over the crash `Universe`; the
schedule vocabulary is fault-agnostic and reused from the core. The
descent is the core's simple form, since `isLeaderBlock_unique` leaves
no twins to tie-break.

Every decision-valued statement concludes on a validator's own view,
caught up to the horizon it reads; the full view is caught up to every
horizon, so the whole-universe reading is the special case.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : Universe Validator BlockId Payload}
variable {T : Finset Validator} {L : BlockId} {s R N : ℕ}

/-! ## The crash fault model -/

/-- The crash fault model: `n ≥ 2f+1` validators, at most `f` of them
crashed. A crashed validator halts — its blocks, while they lasted, are
consistent (`no_equivocation` is universal); only its availability is in
doubt. Safety never consults this class; it exists for liveness alone. -/
class CrashFaults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The crashed validators. Everything else is live. -/
  crashed : Finset Validator
  /-- At most `f` validators crash. -/
  card_crashed : crashed.card ≤ f
  /-- There are at least `2f+1` validators. -/
  card_validators : 2 * f + 1 ≤ Fintype.card Validator

section CrashModel

variable [C : CrashFaults Validator]

/-- The committee is non-empty: at least `2f + 1` validators. -/
theorem CrashFaults.card_pos : 0 < Fintype.card Validator := by
  have := C.card_validators; omega

variable (Validator) in
/-- The live validators: everyone outside the crashed set. -/
def Live : Finset Validator := (C.crashed)ᶜ

@[simp]
theorem mem_live {v : Validator} : v ∈ Live Validator ↔ v ∉ C.crashed := by
  simp [Live]

/-- **The bridge** — the arc's only consumer of the fault bound: the live
class carries the majority quorum, since `n − f ≥ n/2 + 1` whenever
`2f + 1 ≤ n`. -/
theorem majority_le_card_live : majority Validator ≤ (Live Validator).card := by
  have h : (Live Validator).card = Fintype.card Validator - C.crashed.card :=
    Finset.card_compl C.crashed
  have hle : C.crashed.card ≤ Fintype.card Validator := Finset.card_le_univ _
  have h1 := C.card_crashed
  have h2 := C.card_validators
  unfold majority
  omega

end CrashModel

/-! ## Participation and coverage -/

/-! `PopulatedOn` and `SynchronisedOn` are the record's
(`Participation.lean`), at the crash universe's data; `View.full` and
`View.CoversUpto` are the record's (`BlockRecord.lean`). -/

/-! ## Decisions are monotone in the view -/

variable [S : Slots Validator]

/-! Monotonicity in the view and commit propagation are the relation's
(`AnchoredRule.decided_mono`, `decided_full`, at `nemoLaws`). -/

/-! ## A reliable leader commits directly -/

/-- **The commit half.** Post-`R`, a `T`-led slot is directly committed:
coverage makes every `T` block at the decision round reference the leader's
block, and `T` carries the majority. Two populated rounds — propose and
decide, wavelength two. -/
theorem directCommit_of_leader_mem
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ DirectCommit U L (S.slotRound s) := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader s) hlead
  refine ⟨L, ⟨hL, hLr, hLc⟩, ?_⟩
  have hsub : T ⊆ supporters U L (S.slotRound s + 1) := by
    intro w hw
    obtain ⟨b, hb, hbc, hbr⟩ := hpop1 w hw
    refine mem_supporters.mpr ⟨b, hb, hbr, ?_, hbc⟩
    exact hs (S.slotRound s) hR b hb hbr (by rw [hbc]; exact hw)
      L hL hLr (by rw [hLc]; exact hlead)
  exact le_trans hcard (Finset.card_le_card hsub)

omit S in
/-- A view caught up to the decision round sees every supporter, so a
direct commit in the universe is a direct commit in the view. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U} {r : ℕ}
    (h : DirectCommit U L r) (hcov : V.CoversUpto (r + 1)) :
    DirectCommitIn U V L r :=
  HoldsAtLeast.of_coversUpto
    (fun p hp => ⟨(mem_votesFor.mp hp).1, (mem_votesFor.mp hp).2.1.le⟩) hcov h

/-- The commit half, as a decision — on any view caught up to the
decision round. -/
theorem decided_of_leader_mem
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (V : View Validator BlockId Payload U)
    (hcov : V.CoversUpto (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided U V s (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_of_coversUpto hdc hcov)⟩

/-! A run of slots spanning eligibility is the relation's
`AnchoredRule.SpansEligible`; under a pipelined identity-round schedule
`c = 2` spans (`spansEligible_of_identity`), two consecutive reliable
leaders sufficing at wavelength two. -/

/-! ## The two all-of-`Live` cases

The composition itself — a fair schedule decides everything — is
`Nemo.all_decided_below_of_fairRun` in `NemoProperties.lean`, from the
vote support. -/

section Composed

variable [C : CrashFaults Validator]

/-- The all-of-`Live` participation case. -/
abbrev Populated (U : Universe Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Live Validator) r

/-- The all-of-`Live` coverage case. -/
abbrev Synchronised (U : Universe Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Live Validator) R

end Composed

end Nemo

end LeanDag
