import LeanDag.Mysticeti.Liveness
import LeanDag.Mysticeti.Properties
/-!
# Quantitative liveness — bounds, from rated assumptions

`archive/liveness.md` §8 Q3 and Q4. Under the unrated hypotheses `hub` (the
backoff clears any threshold eventually) and `FairScheduleOn` (a
`T`-leader recurs, with no gap bound), no numeric bound exists at all:
a slow enough timeout or a schedule with unbounded gaps between
`T`-leaders defeats any fixed rate. `Rated`, `FairWithin` and
`BoundedSpacing` are the rated replacements that pin an explicit `R`,
a slot bound and a round bound respectively; `Rated` implies `hub`, so
the rated route strengthens one assumption and drops another.
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {D N : ℕ}

/-! ## Part 1 — a rated backoff pins `R`

`archive/liveness.md` §8 Q3. The threshold coverage consumes is
`D + delay ≤ timeout n` for every `n ≥ R`; with a rate the least such
`R` is read off directly (`ViewPace.synchronisedOn_of_rate`). -/

/-- A backoff that grows at least as fast as the round index. Any
schedule dominating the identity qualifies; it rules out growth slow
enough that clearing a fixed threshold takes unboundedly many rounds. -/
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n

/-- **A rated backoff clears any threshold by the threshold itself.**
Monotonicity is not used: the bound at `n` comes from `n` itself, so it
cannot lapse afterwards. -/
theorem backoff_ge_of_rate {timeout : ℕ → ℕ} (hrate : Rated timeout) (m : ℕ) :
    ∀ n, m ≤ n → m ≤ timeout n :=
  fun n hn => le_trans hn (hrate n)

/-- Every rated backoff is unbounded, so `Rated` really is a strengthening
of the retired existential hypothesis rather than a sideways move. -/
theorem unbounded_of_rated {timeout : ℕ → ℕ} (hrate : Rated timeout) :
    ∀ m, ∃ n, m ≤ timeout n :=
  fun m => ⟨m, hrate m⟩

/-! ## Part 2 — a rated schedule pins the committing slot

`archive/liveness.md` §8 Q4. `FairWithin` promises a `T`-leader inside a fixed
window `w`; round-robin over `3f+1` validators supplies `w = f + 1`,
since at most `f` non-`T` validators can be consecutive in the
rotation. -/

variable [S : Slots Validator]

/-- The schedule names a `T`-leader within every window of `w` slots,
the rated form of `FairScheduleOn`. `w` is a property of the schedule
alone, which keeps L6's quantifier order intact. -/
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A rated schedule is a fair one, so everything already proved from
`FairScheduleOn` applies to it unchanged. -/
theorem FairWithin.fairScheduleOn {w : ℕ} (h : FairWithin T w) : FairScheduleOn T :=
  fun k => let ⟨k', hk', _, hlead⟩ := h k; ⟨k', hk', hlead⟩

variable {w : ℕ}

/-- **Q4, the schedule half.** L6 with the committing slot bounded: it
lies within `w` slots of `max k R`, where the slot past round `R` is
named explicitly by `slotAt Validator R` rather than assuming a
coincidence a monotone schedule need not give. -/
theorem commits_recur_within (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k (slotAt Validator R) ≤ k' ∧ k' < max k (slotAt Validator R) + w ∧
      R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload T R k' := by
  obtain ⟨k', hk', hlt, hlead⟩ := fair (max k (slotAt Validator R))
  have hRk' : R ≤ S.slotRound k' :=
    le_trans (le_slotRound_slotAt (Validator := Validator) R)
      (S.mono (le_trans (le_max_right _ _) hk'))
  refine ⟨k', hk', hlt, hRk', ?_⟩
  intro U N hpop hs hN
  exact MysticetiProperties.decided_of_leader_of_populated_of_properties (S := S) hcard hs
    hRk' hpop hN hlead

/-! ### From a slot bound to a round bound

`Slots` bounds slot rounds from below, which is what safety needs; a
latency claim wants the opposite bound, so the round bound needs its
own hypothesis, the mirror image of that spacing. -/

/-- Consecutive slots are at most `s` rounds apart — the upper companion to
such a field. Every real schedule has one; the class omits it because no
safety result ever asks. -/
def BoundedSpacing (s : ℕ) : Prop := ∀ k, S.slotRound (k + 1) ≤ S.slotRound k + s

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Bounded spacing accumulates: `d` slots on costs at most `s * d` rounds. -/
theorem slotRound_le_of_boundedSpacing {s : ℕ}
    (hs : BoundedSpacing (Validator := Validator) s) (k d : ℕ) :
    S.slotRound (k + d) ≤ S.slotRound k + s * d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := hs (k + d)
      have hmul : s * (d + 1) = s * d + s := Nat.mul_succ s d
      calc S.slotRound (k + (d + 1)) = S.slotRound (k + d + 1) := rfl
        _ ≤ S.slotRound (k + d) + s := hstep
        _ ≤ S.slotRound k + s * d + s := by omega
        _ = S.slotRound k + s * (d + 1) := by omega

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A slot bound becomes a round bound. -/
theorem slotRound_le_of_lt {s : ℕ} (hs : BoundedSpacing (Validator := Validator) s)
    {k₀ m k' : ℕ} (hk' : k₀ ≤ k') (hlt : k' < k₀ + m) :
    S.slotRound k' ≤ S.slotRound k₀ + s * m := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k₀ + d := ⟨k' - k₀, by omega⟩
  have hd : d ≤ m := by omega
  have h1 := slotRound_le_of_boundedSpacing (Validator := Validator) hs k₀ d
  have h2 : s * d ≤ s * m := Nat.mul_le_mul_left s hd
  omega

/-- **Q4 in rounds.** The committing slot's round is bounded: the
search starts at `slotRound (max k (slotAt R))`, `s * w` is the
worst-case cost of walking to the next `T`-leader, and `+ 2` is the
certificate round. At the standard settings this reads
`3 * (f + 1)` rounds past the starting slot. Blind to multiple
leaders — `BoundedSpacing s` cannot see that several leaders may share
a round — but the only statement that says anything about an
irregular schedule. -/
theorem commits_recur_by_round {s : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairWithin T w)
    (hs : BoundedSpacing (Validator := Validator) s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k (slotAt Validator R)) + s * w ∧
      R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (max k (slotAt Validator R)) + s * w + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  obtain ⟨k', hk, hlt, hRk', hcommit⟩ :=
    commits_recur_within (BlockId := BlockId) (Payload := Payload) hT hcard fair R k
  have hround := slotRound_le_of_lt (Validator := Validator) hs hk hlt
  refine ⟨k', le_trans (le_max_left k _) hk, hround, hRk', ?_⟩
  intro U N hpop hsync hN
  exact hcommit U N hpop hsync (by omega)

end LeanDag
