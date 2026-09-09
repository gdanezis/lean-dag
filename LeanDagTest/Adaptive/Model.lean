import LeanDag.Adaptive.Basic
import LeanDag.Adaptive.Run
import LeanDag.Adaptive.Liveness
import LeanDag.Integration.AdaptiveMysticeti
import LeanDag.Integration.AdaptiveOdontoceti
import LeanDagTest.Mysticeti.Model
import LeanDagTest.Odontoceti.Model
/-!
# Adaptive leaders, witnessed: the induced instance and the bounded relation

The `U7` universe of `Model.lean` under reassigned leaders. Three things
are exhibited on data before anything is proved from the definitions:

* `slotsOf` genuinely reassigns: under `aSwap`, slot `1` is led by
  validator `1`, its leader block is `13` rather than `12`, and the
  slot's verdict *changes* — the same DAG, read under a different
  assignment, commits a different block. Adaptivity is not a relabelling.
* `DecidedWithin` derives real verdicts at real bounds: the direct
  commit at slot `1` and the indirect commit at slot `0` (anchor `1`,
  the `Model.lean` configuration) both fit within bound `2`.
* `decidedWithin_congr` transports a bounded verdict across assignments
  that differ only above the bound — the exact situation of an epoch
  judged against a schedule whose later epochs are not yet determined.
-/

namespace LeanDagTest

open LeanDag

/-- One leader per round on the `U7` schedule: slot rounds are `3k`. -/
theorem u7_inj : Function.Injective (Slots.slotRound (Validator := Fin 4)) := by
  intro a b h
  change 3 * (a / 1) = 3 * (b / 1) at h
  omega

/-- The base assignment, as a plain function. -/
def aBase : ℕ → Fin 4 := fun _ => 0

/-- Slot `1`'s leader moves to validator `1`; everything else unchanged. -/
def aSwap : ℕ → Fin 4 := fun k => if k = 1 then 1 else 0

/-- An assignment differing from the base only at slots `≥ 2`. -/
def aHigh : ℕ → Fin 4 := fun k => if 2 ≤ k then 1 else 0

-- The induced instance reassigns the leader and keeps the rounds.
example : (slotsOf u7_inj aSwap).leader 1 = 1 := rfl
example : (slotsOf u7_inj aSwap).slotRound 1 = 3 := rfl

-- Under the base assignment the induced instance *is* the instance.
example : slotsOf u7_inj (Slots.leader (Validator := Fin 4)) =
    (inferInstance : Slots (Fin 4)) := slotsOf_base u7_inj

-- Under `aSwap`, slot 1's candidate is block 13, not block 12.
example : IsLeaderBlock (S := slotsOf u7_inj aSwap) U7 1 13 := by decide
example : ¬ IsLeaderBlock (S := slotsOf u7_inj aSwap) U7 1 12 := by decide

/-- The bounded direct commit at slot `1`, base assignment, bound `2`. -/
theorem u7_decidedWithin_slot1 :
    DecidedWithin (S := slotsOf u7_inj aBase) U7 V7 2 1 (some 12) :=
  DecidedWithin.directCommit (by omega) (by decide) (by decide)

/-- The bounded indirect commit at slot `0`, anchored on slot `1` — the
`Model.lean` configuration, now with both slots inside bound `2`. -/
theorem u7_decidedWithin_slot0 :
    DecidedWithin (S := slotsOf u7_inj aBase) U7 V7 2 0 (some 0) :=
  AnchoredRule.DecidedWithin.indirectCommit_single rfl (fun _ _ h => h) (j := 1) (A := 12)
    (by omega) (by omega) (by decide)
    u7_decidedWithin_slot1
    (fun _ h1 h2 _ => absurd h2 (by omega))
    (by decide)
    (show CertifiedIn U7 12 0 _ from ⟨8, by decide, Reaches.single (by decide)⟩)

-- The structural lemmas, exercised.
example : Decided (S := slotsOf u7_inj aBase) U7 V7 1 (some 12) :=
  u7_decidedWithin_slot1.toDecided
example : (1 : ℕ) < 2 := u7_decidedWithin_slot1.lt_bound
example : DecidedWithin (S := slotsOf u7_inj aBase) U7 V7 5 1 (some 12) :=
  u7_decidedWithin_slot1.mono (by omega)

/-- Congruence across the bound: `aHigh` differs from the base only at
slots the bound excludes, so the slot-`0` verdict transports. -/
theorem u7_decidedWithin_slot0_high :
    DecidedWithin (S := slotsOf u7_inj aHigh) U7 V7 2 0 (some 0) :=
  decidedWithin_congr
    (fun m hm => by unfold aBase aHigh; rw [if_neg (by omega)])
    u7_decidedWithin_slot0

/-- **The verdict moves with the assignment.** Under `aSwap` the slot-`1`
candidate is block `13`, and the view commits it directly: the same DAG,
under a reassigned leader, decides a different block for the slot. -/
theorem u7_decidedWithin_slot1_swap :
    DecidedWithin (S := slotsOf u7_inj aSwap) U7 V7 2 1 (some 13) :=
  DecidedWithin.directCommit (S := slotsOf u7_inj aSwap) (by omega) (by decide) (by decide)

#print axioms u7_decidedWithin_slot0
#print axioms u7_decidedWithin_slot1_swap

/-! ## A partial adaptive run, and agreement exercised

`demotePolicy` is genuinely adaptive at epoch length `1`: a slot whose
verdict two slots below was a skip is handed to validator `1`.

**The run is partial, and it cannot be total.** `U7` is finite, its top
round is `5`, and a skip asks for a quorum of blockers at the slot's
voting round — so no slot past the frontier can be decided at all, and
the runs below close at height `2`. A total run needs a DAG populated
at every round, which is exactly the hypothesis `adaptiveRun_exists`
carries. Reassignment is therefore exhibited on `pick` rather than on a
run's `assign`: `vd7` records a skip at slot `2` as an *input* the
policy reads, not as a verdict `U7` settles.

A second run over the trimmed view `V7small` holds the same verdicts,
and `partialRun_agree` is exercised on the pair. -/

/-- Every `U7` block sits at round `5` or below: slots past the frontier
have no candidates. -/
theorem u7_round_le : ∀ L : Fin 24, (U7.block L).round ≤ 5 := by decide

/-- Demote-on-skip at epoch length `1`: slot `k`'s leader consults the
verdict of slot `k − 2` and nothing else. -/
def demotePolicy : AdaptivePolicy (Fin 4) (Fin 24) Unit where
  W := 1
  W_pos := Nat.one_pos
  inj := u7_inj
  pick := fun _ _ v k => if k < 2 then 0 else if v (k - 2) = none then 1 else 0
  adapted := by
    intro U V₁ V₂ v w k hvw
    by_cases h2 : k < 2
    · simp only [if_pos h2]
    · have hj : v (k - 2) = w (k - 2) := hvw (k - 2) (by simp only [epochOf]; omega)
      simp only [if_neg h2, hj]
  base_prefix := by
    intro U V v k hk
    have h2 : k < 2 := by simpa [epochOf] using hk
    simp only [if_pos h2]
    rfl

/-- The verdicts fed to the policy: the two slots `U7` decides, and
`none` above the frontier — the latter an input the policy reads, which
this finite universe does not itself settle. -/
def vd7 : ℕ → Option (Fin 24) :=
  fun k => if k = 0 then some 0 else if k = 1 then some 12 else none

/-- The adaptive run over the full view, closed to height `2`. -/
def run7 : PartialRun demotePolicy U7 V7 2 where
  assign := fun k => demotePolicy.pick U7 V7 vd7 k
  vdct := vd7
  closed := by
    intro k hk
    have hk2 : k < 2 := by
      have hW : demotePolicy.W = 1 := rfl
      simpa [hW, epochOf] using hk
    interval_cases k
    · have hB : demotePolicy.W * (epochOf demotePolicy.W 0 + 2) = 2 := rfl
      rw [hB]
      exact AnchoredRule.decidedBelow_of_decidedWithin coreLaws trivial
        (S := slotsOf demotePolicy.inj (fun k => demotePolicy.pick U7 V7 vd7 k))
        (decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          u7_decidedWithin_slot0)
    · have hB : demotePolicy.W * (epochOf demotePolicy.W 1 + 2) = 3 := rfl
      rw [hB]
      exact AnchoredRule.decidedBelow_of_decidedWithin coreLaws trivial
        (S := slotsOf demotePolicy.inj (fun k => demotePolicy.pick U7 V7 vd7 k))
        (decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          (u7_decidedWithin_slot1.mono (by omega)))
  coherent := fun _ _ => rfl

/-- The same run over the trimmed view `V7small`. -/
def run7small : PartialRun demotePolicy U7 V7small 2 where
  assign := fun k => demotePolicy.pick U7 V7small vd7 k
  vdct := vd7
  closed := by
    intro k hk
    have hk2 : k < 2 := by
      have hW : demotePolicy.W = 1 := rfl
      simpa [hW, epochOf] using hk
    interval_cases k
    · have hB : demotePolicy.W * (epochOf demotePolicy.W 0 + 2) = 2 := rfl
      rw [hB]
      exact AnchoredRule.decidedBelow_of_decidedWithin coreLaws trivial
        (S := slotsOf demotePolicy.inj (fun k => demotePolicy.pick U7 V7small vd7 k))
        (decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
        (AnchoredRule.DecidedWithin.indirectCommit_single rfl (fun _ _ h => h)
          (S := slotsOf u7_inj aBase)
          (j := 1) (A := 12) (by omega) (by omega) (by decide)
          (DecidedWithin.directCommit (S := slotsOf u7_inj aBase)
            (by omega) (by decide) (by decide))
          (fun _ h1 h2 _ => absurd h2 (by omega))
          (by decide)
          (show CertifiedIn U7 12 0 _ from ⟨8, by decide, Reaches.single (by decide)⟩)))
    · have hB : demotePolicy.W * (epochOf demotePolicy.W 1 + 2) = 3 := rfl
      rw [hB]
      exact AnchoredRule.decidedBelow_of_decidedWithin coreLaws trivial
        (S := slotsOf demotePolicy.inj (fun k => demotePolicy.pick U7 V7small vd7 k))
        (decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          ((DecidedWithin.directCommit (S := slotsOf u7_inj aBase) (B := 2)
            (by omega) (by decide) (by decide)).mono (by omega)))
  coherent := fun _ _ => rfl

-- **The policy genuinely adapts**: a skip two slots below moves the
-- leader off the base rotation. Read off `pick`, since `U7` settles no
-- slot past the frontier and so no run's `assign` is justified there.
example : demotePolicy.pick U7 V7 vd7 4 = 1 := rfl
example : demotePolicy.pick U7 V7 vd7 3 = 0 := rfl

-- **Safety exercised**: the two views' runs agree on their common
-- epochs, verdicts and schedule.
example : ∀ k, epochOf demotePolicy.W k < 2 → run7.vdct k = run7small.vdct k :=
  fun k hk => partialRun_agree run7 run7small k (by simpa using hk)
example : ∀ m, epochOf demotePolicy.W m < 3 → run7.assign m = run7small.assign m :=
  fun m hm => partialRun_assign_agree run7 run7small m (by simpa using hm)

/-! ## The liveness clauses, witnessed -/

/-- Three-round spacing spans at `c = 1`: a single committed slot
anchors everything below it. The schedule-shape hypothesis the adaptive
existence consumes, on this schedule. -/
theorem u7_spansEligible : SpansEligibleAt (Validator := Fin 4) 2 1 := by
  intro b i hi
  change 3 * (i / 1) + 2 < 3 * ((b + 1 - 1) / 1)
  omega

/-- The demote policy names only validators `0` and `1`, whatever it
reads, so it places a (one-slot) run in every epoch for `T = {0, 1}`:
`PlacesRuns`, witnessed. -/
theorem demote_placesRuns : PlacesRuns demotePolicy {0, 1} 1 := by
  intro U V v e
  have hW : demotePolicy.W = 1 := rfl
  refine ⟨e + 1, by rw [hW]; omega, by rw [hW]; omega, ?_⟩
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hp : demotePolicy.pick U V v (e + 1 + 0) =
      if e + 1 + 0 < 2 then 0 else if v (e + 1 + 0 - 2) = none then 1 else 0 := rfl
  rw [hp]
  split_ifs <;> decide

#print axioms LeanDag.adaptiveRun_agree
#print axioms LeanDag.adaptiveRun_exists
#print axioms LeanDag.AdaptivePolicy.const_run_decided
#print axioms run7
#print axioms demote_placesRuns

/-! ## The two-round mirror, witnessed

The bounded Odontoceti relation on the `Uodo`/`Uskip` families of
`Odontoceti/Model.lean`: the direct commit at a bound, the reassignment
moving a slot's committed block (`8`, not `7` — six validators, so the
donor of the reassigned identity has a block in every round), and the
indirect commit *with its canonicity clause* carried through the bound —
the constructor the three-round relation does not have. -/

/-- One leader per round on the Odontoceti schedule: rounds are `k`. -/
theorem odo_inj : Function.Injective (odoSlots.slotRound) := by
  intro a b h
  change 1 * (a / 1) = 1 * (b / 1) at h
  omega

/-- The base rotation, as a plain function. -/
def oBase : ℕ → Fin 6 := fun k => ⟨k % 6, by omega⟩

/-- Slot `1`'s leader moves to validator `2`. -/
def oSwap : ℕ → Fin 6 := fun k => if k = 1 then 2 else oBase k

/-- The bounded two-round direct commit at slot `1`, base rotation. -/
theorem uodo_decidedWithin_slot1 :
    Odontoceti.DecidedWithin (S := slotsOf odo_inj oBase)
      Uodo (View.full Uodo) 2 1 (some 7) :=
  Odontoceti.DecidedWithin.directCommit (S := slotsOf odo_inj oBase)
    (by omega) (by decide) (by decide)

/-- **The verdict moves with the assignment, two-round rule**: under
`oSwap` the slot-`1` candidate is block `8`, and it commits directly. -/
theorem uodo_decidedWithin_slot1_swap :
    Odontoceti.DecidedWithin (S := slotsOf odo_inj oSwap)
      Uodo (View.full Uodo) 2 1 (some 8) :=
  Odontoceti.DecidedWithin.directCommit (S := slotsOf odo_inj oSwap)
    (by omega) (by decide) (by decide)

-- The embedding and agreement, exercised on the two-round side.
example : Odontoceti.Decided Uodo (View.full Uodo) 1 (some 7) :=
  uodo_decidedWithin_slot1.toDecided
example : some (7 : Fin 24) = some 7 :=
  AnchoredRule.DecidedWithin.agree Odontoceti.odontocetiLaws trivial (S := slotsOf odo_inj oBase)
    uodo_decidedWithin_slot1 uodo_decidedWithin_slot1

/-- **The canonicity clause through the bound**: `Uskip`'s slot `1` is
undecided directly and commits through the slot-`3` anchor as the least
passing candidate — the `Odontoceti.DecidedWithin.indirectCommit`
constructor in full, inside bound `4`. -/
theorem uskip_decidedWithin_slot1 :
    Odontoceti.DecidedWithin (S := slotsOf odo_inj oBase)
      Uskip (View.full Uskip) 4 1 (some 7) := by
  refine Odontoceti.DecidedWithin.indirectCommit (S := slotsOf odo_inj oBase)
    (j := 3) (A := 21) (i := 0) (by omega) (by omega) (by decide)
    (Odontoceti.DecidedWithin.directCommit (S := slotsOf odo_inj oBase)
      (by omega) (by decide) (by decide))
    ?_ (by decide) (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 2 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro L' hL' ht' hlt
    have hall : ∀ M : Fin 36,
        IsLeaderBlock (S := odoSlots) Uskip 1 M → M = 7 := by decide
    have := hall L' hL'
    subst this
    exact absurd (show (7 : Fin 36) < 7 from hlt) (lt_irrefl _)

/-- Congruence on the two-round side: an assignment differing only
above the bound derives the same verdict. -/
example :
    Odontoceti.DecidedWithin (S := slotsOf odo_inj (fun k => if 4 ≤ k then 0 else oBase k))
      Uskip (View.full Uskip) 4 1 (some 7) :=
  AnchoredRule.decidedWithin_slotsOf_congr Odontoceti.odontocetiLaws trivial
    (fun m hm => by rw [if_neg (by omega)])
    uskip_decidedWithin_slot1

#print axioms LeanDag.Odontoceti.adaptiveRun_agree
#print axioms LeanDag.Odontoceti.adaptiveRun_exists
#print axioms uskip_decidedWithin_slot1

end LeanDagTest
