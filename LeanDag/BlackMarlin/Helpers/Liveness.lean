import LeanDag.BlackMarlin.Liveness.Statement
import LeanDag.BlackMarlin.Helpers.Decision
/-!
# Black Marlin — the liveness layer

Generated proof layer; not part of the audit surface. The lemmas behind
`Liveness/Statement.lean`. The counting is the core's: `VotesAt` is what
a quorum of reliable authors supplies at the round above a block, and
`votesAt_of_synchronisedOn` derives it from coverage. What this file adds
is the second reading of that same fact at the round above, which is what
the link clause of the rule asks for.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {R r : ℕ} {L : BlockId}

/-! ## The support step -/

omit Rot in
/-- **The counting step**, the core's `directCommit_of_votesAt` at this
arc's `Supported` — the same predicate under another name, so the proof
is the same three lines. A quorum-sized `T` whose blocks one round above
`r` all reference `L` supports it. -/
theorem supported_of_votesAt (hcard : quorumCard Validator ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1)) (hv : VotesAt U T r L) :
    Supported U L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨b, hb, hbc, hbr⟩ := hpop1 w hw
  exact mem_supporters.mpr ⟨b, hb, hbr, hv w hw b hb hbc hbr, hbc⟩

omit Rot in
/-- A reliable author's block is supported: coverage makes every reliable
block one round up reference it, and those authors carry a quorum.
Stated on a bare block rather than on an anchor, because the inclusion
result needs it of blocks that anchor nothing. -/
theorem supported_of_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ r) (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T) :
    Supported U L r :=
  supported_of_votesAt hcard hpop1 (votesAt_of_synchronisedOn hs hR hL hLr hLc)

/-- A reliably anchored round has a supported anchor. -/
theorem exists_supported_anchor (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ r)
    (hpop : PopulatedOn U T r) (hpop1 : PopulatedOn U T (r + 1))
    (hlead : Rot.anchor r ∈ T) :
    ∃ L, IsAnchor U r L ∧ Supported U L r := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop (Rot.anchor r) hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    supported_of_mem hcard hs hR hpop1 hL hLr (by rw [hLc]; exact hlead)⟩

/-! ## The commit step -/

/-- **BML1.** Two consecutive reliably anchored rounds, over three
populated rounds, are committed — the link costing no further hypothesis,
since the coverage fact supporting the round-`r` anchor already makes
the round-`(r+1)` anchor reference it. -/
theorem committed_of_run (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ r)
    (hpop : PopulatedOn U T r) (hpop1 : PopulatedOn U T (r + 1))
    (hpop2 : PopulatedOn U T (r + 2))
    (hlead : Rot.anchor r ∈ T) (hlead1 : Rot.anchor (r + 1) ∈ T) :
    ∃ L, IsAnchor U r L ∧ Committed U L r := by
  obtain ⟨L, haL, hsL⟩ := exists_supported_anchor hcard hs hR hpop hpop1 hlead
  obtain ⟨L', haL', hsL'⟩ :=
    exists_supported_anchor hcard hs (by omega) hpop1 hpop2 hlead1
  refine ⟨L, haL, haL, hsL, ⟨L', mem_linkers.mpr ⟨haL', ?_, hsL'⟩⟩⟩
  exact votesAt_of_synchronisedOn hs hR haL.1 haL.2.1 (by rw [haL.2.2]; exact hlead)
    (Rot.anchor (r + 1)) hlead1 L' haL'.1 haL'.2.2 haL'.2.1

/-! ## The full view -/

omit Rot in
/-- So it counts the same quorum. -/
theorem supportedIn_full : SupportedIn U (View.full U) L r ↔ Supported U L r := by
  unfold SupportedIn Supported supportersIn supporters
  rw [heldAuthors_full fun _ hq => (mem_votesFor.mp hq).1]

/-- And it holds every linking anchor there is. -/
theorem linkersIn_full : linkersIn U (View.full U) L r = linkers U L r := by
  ext L'
  simp only [linkersIn, linkers, Finset.mem_inter, Finset.mem_filter, supportedIn_full]
  constructor
  · rintro ⟨⟨hb, hrest⟩, -⟩
    exact ⟨hb, hrest⟩
  · rintro ⟨hb, hrest⟩
    exact ⟨⟨hb, hrest⟩, (mem_blocksAt.mp hb).1⟩

/-- **BML2.** The rule and the full view's reading of it coincide. -/
theorem committedIn_full_iff :
    CommittedIn U (View.full U) L r ↔ Committed U L r := by
  unfold CommittedIn Committed LinkedIn Linked
  rw [supportedIn_full, linkersIn_full]

/-! ## Inclusion -/

omit Rot in
/-- **BML3.** A reliable author's block lies in the causal history of
every block two rounds above it, from coverage and BM2 alone — no
clause of the commit rule is consumed. -/
theorem mem_history_of_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ r) (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    L ∈ history U c :=
  (mem_history_iff hc).mpr
    (reaches_of_supported (supported_of_mem hcard hs hR hpop1 hL hLr hLc) hc hcr)

/-! ## Recurrence -/

/-- **BML4.** Under a recurring run of two, the rotation names a round —
before any DAG is fixed — that every DAG grown two rounds past it and
covered from `R` commits. -/
theorem recurrence (hcard : quorumCard Validator ≤ T.card)
    (hfair : Liveness.FairRun T 2) :
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ Liveness.CommitsAtRound BlockId Payload T R r' := by
  obtain ⟨r', hr', hrun⟩ := hfair (max r R)
  have hRr' : R ≤ r' := le_trans (le_max_right r R) hr'
  refine ⟨r', le_trans (le_max_left r R) hr', hRr', ?_⟩
  intro U N hpop hs hN
  exact committed_of_run hcard hs hRr'
    (hpop r' hRr' (by omega)) (hpop (r' + 1) (by omega) (by omega))
    (hpop (r' + 2) (by omega) (by omega))
    (by simpa using hrun 0 (by omega)) (by simpa using hrun 1 (by omega))

/-! ## The rotation is fair

The core's `FairRunOn` needs runs of three and stays an assumption;
Black Marlin's runs of two are short enough to prove by counting — two
cyclically adjacent unreliable anchors would inject the reliable set
into the Byzantine one.
-/

section RoundRobin

variable (n : ℕ) (hn : 0 < n)

/-- The cyclic successor on `Fin n` — the rotation's step. -/
private def nxt (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The step is injective, which is what turns "no adjacent pair is
reliable" into a cardinality bound. -/
private theorem nxt_inj : Function.Injective (nxt n hn) := by
  intro i j hij
  have h : (i.val + 1) % n = (j.val + 1) % n := congrArg Fin.val hij
  have hi := i.isLt
  have hj := j.isLt
  refine Fin.ext ?_
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1 <;>
    rcases Nat.lt_or_ge (j.val + 1) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · have hj' : j.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h1, hj', Nat.mod_self] at h; omega
  · have hi' : i.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h2, hi', Nat.mod_self] at h; omega
  · omega

/-- **Two cyclically adjacent validators are both reliable.** Were there
none, the successor map would inject the reliable set into the Byzantine
one, giving `n - f <= f` against `3f + 1 <= n`. -/
private theorem exists_adjacent_correct [F : Faults (Fin n)] :
    ∃ i : Fin n, i ∈ (Correct : Finset (Fin n)) ∧
      nxt n hn i ∈ (Correct : Finset (Fin n)) := by
  by_contra hcon
  push Not at hcon
  have hsub : (Correct : Finset (Fin n)).image (nxt n hn) ⊆ F.byzantine := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    simpa using hcon i hi
  have himg := Finset.card_image_of_injective (Correct : Finset (Fin n)) (nxt_inj n hn)
  have h1 := Finset.card_le_card hsub
  have h2 := card_correct (Validator := Fin n)
  have h3 := F.card_byzantine
  have h4 := F.card_validators (Validator := Fin n)
  omega

/-- **BML5.** Round-robin puts two consecutive reliable anchors
arbitrarily far out, at every committee and whichever validators are
Byzantine. The pair recurs once per cycle, which is what carries it past
any given round. -/
theorem roundRobin_fairRun [F : Faults (Fin n)] :
    Liveness.FairRun (Rot := Liveness.roundRobin n hn) (Correct : Finset (Fin n)) 2 := by
  obtain ⟨i, hi, hi1⟩ := exists_adjacent_correct n hn
  intro r
  refine ⟨i.val + n * r, ?_, ?_⟩
  · have : r ≤ n * r := Nat.le_mul_of_pos_left r hn
    omega
  · intro k hk
    have e0 : (Liveness.roundRobin n hn).anchor (i.val + n * r + 0) = i := by
      refine Fin.ext ?_
      change (i.val + n * r + 0) % n = i.val
      rw [Nat.add_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
    have e1 : (Liveness.roundRobin n hn).anchor (i.val + n * r + 1) = nxt n hn i := by
      refine Fin.ext ?_
      change (i.val + n * r + 1) % n = (i.val + 1) % n
      rw [show i.val + n * r + 1 = i.val + 1 + n * r by omega, Nat.add_mul_mod_self_left]
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · rw [e0]; exact hi
    · rw [e1]; exact hi1

end RoundRobin

/-! ## When the support *is* in view

The repairs read `Supported`, a fact about the universe, where a
validator reads its own view. They agree at a reliable author's anchor
past the round coverage takes hold, since coverage puts the quorum in
view — not the case the repair needs, since for a Byzantine anchor
coverage says nothing. -/

/-- **A reliable author's anchor is seen as supported**, by any view that
holds the reliable blocks of the round above, once coverage has taken
hold. -/
theorem supportedIn_of_synchronised {T : Finset Validator} {R ρ : ℕ}
    {V : View Validator BlockId Payload U}
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ ρ) (hpop : PopulatedOn U T (ρ + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = ρ)
    (hLc : (U.block L).creator ∈ T)
    (hheld : ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = ρ + 1 →
      b ∈ V.ids) :
    SupportedIn U V L ρ := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro u hu
  obtain ⟨c, hc, hcc, hcr⟩ := hpop u hu
  refine mem_creatorsOf.mpr ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩, hcc⟩
  · exact Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, hcr⟩,
      votesAt_of_synchronisedOn hs hR hL hLr hLc u hu c hc hcc hcr⟩
  · exact hheld c hc (hcc ▸ hu) hcr

end BlackMarlin

end LeanDag
