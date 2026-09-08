import LeanDag.Mysticeti.ViewPace
import LeanDag.DoS.Novelty
import Mathlib.Tactic.Ring

/-!
# The delivery layer a pacing structure induces

`PaceCore.holds` (report §6.9) is time-indexed; `Delivery.held` (§§8–9)
is round-indexed, reading what `v` held of round `n` when it built its
round-`(n+1)` block. A `ViewPace` induces a `Delivery` by reading the
round-indexed notion at the build instant,
`held v n := (holds v (built v (n+1))).filter (round · = n)`, so every
field of `Delivery` becomes a theorem: `accepted_inj` follows from P7
and P2 collapsing two blocks by one author, and `includes` is P7 at the
build instant. The construction is stated at `T := Correct`. It does
not show the converse — a `Delivery` has no instants to recover a
schedule from.
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {N : ℕ}

namespace ViewPace

variable (vp : ViewPace U (Correct : Finset Validator) N)

/-- **The round-indexed reading of `holds`**: what `v` held of round `n` at
the instant it built its round-`(n+1)` block. Above the horizon there is no
build to read, and the set is empty. -/
def heldOf (v : Validator) (n : ℕ) : Finset BlockId :=
  if n < N then (vp.holds v (vp.built v (n + 1))).filter (fun b => (U.block b).round = n)
  else ∅

/-- What a validator builds on. A correct validator builds on everything it
held --- it has no reason to discard, and P7 obliges it to reference all of
it; nothing is claimed of a Byzantine validator, whose acceptance is left
empty because no clause of the pacing structure constrains it. -/
def acceptedOf (v : Validator) (n : ℕ) : Finset BlockId :=
  if v ∈ (Correct : Finset Validator) then vp.heldOf v n else ∅

omit [DecidableEq BlockId] in
theorem mem_heldOf {v : Validator} {n : ℕ} {b : BlockId} (hn : n < N) :
    b ∈ vp.heldOf v n ↔
      b ∈ vp.holds v (vp.built v (n + 1)) ∧ (U.block b).round = n := by
  simp [heldOf, hn, Finset.mem_filter]

/-- **The acceptance rule is derived** (V19). A correct validator never
holds two blocks by one author at a build instant, not by
deduplication but because P7 would oblige its block to reference both
and P2 forbids that. The storage development assumes this; here it is
a theorem. -/
theorem heldOf_inj {v : Validator} (hv : v ∈ (Correct : Finset Validator))
    {n : ℕ} (hn : n < N) {i j : BlockId}
    (hi : i ∈ vp.heldOf v n) (hj : j ∈ vp.heldOf v n)
    (hij : (U.block i).creator = (U.block j).creator) : i = j := by
  -- the builder's own block at the round above
  obtain ⟨c, hc, hcc, hcr⟩ :=
    vp.populatedOn card_correct (n + 1) (by omega) v hv
  obtain ⟨hi_hold, hi_round⟩ := (vp.mem_heldOf hn).mp hi
  obtain ⟨hj_hold, hj_round⟩ := (vp.mem_heldOf hn).mp hj
  -- P7 puts both into its references
  have hi_ref := vp.references v hv n hn c hc hcc hcr i hi_hold hi_round
  have hj_ref := vp.references v hv n hn c hc hcc hcr j hj_hold hj_round
  -- P2 collapses them
  exact (U.valid c hc).distinct_creators i hi_ref j hj_ref hij

/-- **A pacing structure induces a delivery layer** (V19): every field
discharged from the pacing clauses, so the storage arcs of report
§§8–9 run over an execution liveness actually produces. -/
def toDelivery : Delivery U where
  held := vp.heldOf
  held_spec := by
    intro v n i hi
    by_cases hn : n < N
    · obtain ⟨hhold, hround⟩ := (vp.mem_heldOf hn).mp hi
      exact ⟨vp.holds_sub v _ hhold, hround⟩
    · simp [heldOf, hn] at hi
  accepted := vp.acceptedOf
  accepted_sub := by
    intro v n
    unfold acceptedOf
    split
    · exact Finset.Subset.rfl
    · exact Finset.empty_subset _
  accepted_inj := by
    intro v n i hi j hj hij
    unfold acceptedOf at hi hj
    split at hi
    · rename_i hv
      by_cases hn : n < N
      · exact vp.heldOf_inj hv hn hi (by simpa [acceptedOf, hv] using hj) hij
      · simp [heldOf, hn] at hi
    · simp at hi
  accepts_correct := by
    intro v hv n a ha _
    simpa [acceptedOf, hv] using ha
  includes := by
    intro v hv n b hb hbc hbr
    unfold acceptedOf
    rw [if_pos hv]
    intro a ha
    by_cases hn : n < N
    · obtain ⟨hhold, hround⟩ := (vp.mem_heldOf hn).mp ha
      exact vp.references v hv n hn b hb hbc hbr a hhold hround
    · simp [heldOf, hn] at ha

/-- The induced layer reads the pacing structure's own holdings: what it
records at round `n` is exactly what the validator held of that round when
it built above it. Below the horizon this is a definitional unfolding, and
it is what makes the identification more than a coincidence of types. -/
theorem toDelivery_held {v : Validator} {n : ℕ} (hn : n < N) :
    vp.toDelivery.held v n =
      (vp.holds v (vp.built v (n + 1))).filter (fun b => (U.block b).round = n) := by
  simp [toDelivery, heldOf, hn]

/-! ## The reference discipline, both ways

The storage arcs take one hypothesis beyond `Delivery`: `RefsAccepted`,
that a correct validator references only what it accepted — the
converse of P7, which only obliges a builder to include what it holds
and says nothing about what else it may cite. The trunk supplies it
directly, as `refs_held` (S5). -/

/-- **The reference discipline transfers** to the induced layer: a
correct validator's block references only what it accepted, since
`accepted` is what it held and `refs_held` says its references are
among those. -/
theorem refsAccepted_toDelivery : RefsAccepted vp.toDelivery := by
  intro w hw n b hb hbc hbr
  have hn : n < N := by have := vp.rounds_le b hb; omega
  intro a ha
  have hround : (U.block a).round = n := by
    have := (U.valid b hb).predecessor a ha
    omega
  have : a ∈ vp.holds w (vp.built w (n + 1)) :=
    vp.refs_held w hw n b hb hbc hbr ha
  simpa [toDelivery, acceptedOf, hw] using (vp.mem_heldOf hn).mpr ⟨this, hround⟩

/-- **Liveness and bounded storage, from one structure** (V20). A
pacing structure run under the enforceable acceptance budget gives the
denial-of-service capstone of report §8 outright: no correct validator
stalls, and no correct validator's retained view grows faster than
linearly in the round. Production and the reference discipline are
derived, so the only thing assumed beyond the pacing structure is the
budget itself. -/
theorem dos_resistance_of_pace {κ : ℕ}
    (hu : UniformBudget vp.toDelivery κ) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto vp.toDelivery v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ))) :=
  dos_resistance (vp.populatedOn card_correct) hu vp.refsAccepted_toDelivery

/-- **The same bound, factored** (V20′). The three summands of
`dos_resistance_of_pace` are one product: a correct validator's
retained view grows at `|Correct| * (1 + f * κ)` blocks per round,
over a constant offset of `|Correct| * (1 + f)`. -/
theorem dos_resistance_of_pace' {κ : ℕ}
    (hu : UniformBudget vp.toDelivery κ) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto vp.toDelivery v n).card ≤
          (Correct : Finset Validator).card * ((1 + F.f * κ) * n + 1 + F.f) := by
  obtain ⟨hpop, hview⟩ := vp.dos_resistance_of_pace hu
  refine ⟨hpop, fun v hv n => ?_⟩
  have h := hview v hv n
  have harith :
      (Correct : Finset Validator).card * (n + 1) +
          ((Correct : Finset Validator).card * F.f +
            n * ((Correct : Finset Validator).card * (F.f * κ)))
        = (Correct : Finset Validator).card * ((1 + F.f * κ) * n + 1 + F.f) := by
    ring
  omega

end ViewPace

end LeanDag
