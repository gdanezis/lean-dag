import LeanDag.Mysticeti.Rule
import LeanDag.Common.Participation
import LeanDag.Network.Delivery
/-!
# Liveness — results needing no new primitives

Results **L0**–**L3**. L0 (the DAG cannot grow tall
and thin, from validity alone), L2 (decisions are monotone in the
view) and L3 (commit propagation, L2 at the full view) assume neither
`Live` nor `Synchronised`; L1 (no stall) is the first result needing
`Live`, and still needs no synchrony.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {N : ℕ}

omit [DecidableEq BlockId] in
omit [DecidableEq BlockId] in
omit [DecidableEq BlockId] in
/-! ## L1 — no stall

`Correct` means only *does not equivocate*,
a purely negative condition a crashed validator satisfies too, so
liveness needs a positive rule, `Live`. It is an explicit argument
rather than a class, unlike the universal `Faults`: L0, L2 and L3 do
without it, and folding it into `Faults` would give every safety
theorem a hypothesis it does not use.
-/

/-! **What L4 actually needs of a round** is `PopulatedOn`
(`Participation.lean`): every validator in `T` has a block there, local
and finite, which keeps the horizon `N` out of L4 entirely. `T` rather
than all of `Correct`, since L4 needs only a quorum and demanding all
of `Correct` would make the theorem lapse if a single one misses a
single round. -/

/-! ## L2 — decisions are monotone in the view

If `V ⊆ V'` then every verdict `V` reaches, `V'`
reaches too: combined with M1, a validator never revises a decision as
its view grows. This works only because `CertifiedIn` is universe-level
— were it view-relative, the `indirectSkip` case's negative premise
would be anti-monotone, and growing the view could flip a skip into a
commit.
-/

variable [S : Slots Validator]

/-! **L2** and **L3** (commit propagation) are the relation's
`decided_mono` and `decided_full` at `coreLaws`. -/

/-! ## L3 — commit propagation

Eventual DAG synchrony says anything one
correct validator holds, all eventually hold, so every correct
validator's eventual view is the full view and L3 is L2 instantiated
there. -/

/-! **A view caught up to round `N`** is `View.CoversUpto`: it holds
every block of the universe at a round at or below `N`, the hypothesis
under which a liveness result holds of a validator's own view rather
than the full one; `View.coversUpto_full` says the full view satisfies
it at every `N`. -/

/-! ## L4 — a correct leader commits

Two layers of coverage: every correct round-`(r+1)`
block references correct-authored `L`, every correct round-`(r+2)`
block then references all of those, so its votes for `L` form a
quorum and it certifies, and the certificates themselves come from a
quorum. Only correct-to-correct coverage is used, and the hypotheses
are three local `Populated` facts with no horizon or growth. -/

variable {L C : BlockId} {R r : ℕ} {k : ℕ} {T : Finset Validator}

omit S in
/-- **What the three-round rule counts**: every `T`-authored block at the
decision round certifies `L`. Coverage implies it through the vote layer
(`certifiesAt_of_synchronisedOn`); the reactive certificate wait supplies
it directly (`ReactiveM.certifies`). -/
def CertifiesAt (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 2 → Certifies U c L

omit S in
/-- A correct round-`(r+2)` block certifies any correct round-`r` block,
once round `r+1` is populated and synchrony has taken hold: both layers
of coverage at once. -/
theorem certifies_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2)
    (hCc : (U.block C).creator ∈ T) :
    Certifies U C L := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
  have hqcorrect : (U.block q).creator ∈ T := by rw [hqc]; exact hv
  rw [mem_creatorsOf]
  refine ⟨q, ?_, hqc⟩
  simp only [votesIn, carriedVotes, Finset.mem_filter]
  exact ⟨hs (r + 1) (by omega) C hC (by omega) hCc q hq hqr hqcorrect,
         hs r hRr q hq hqr hqcorrect L hL hLr hLc⟩

omit S in
/-- Coverage gives the certificates, through the vote layer: the
`CertifiesAt` form of the lemma above. -/
theorem certifiesAt_of_synchronisedOn
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) :
    CertifiesAt U T r L :=
  fun _v hv C hC hCc hCr =>
    certifies_of_synchronisedOn hcard hs hRr hpop1 hL hLr hLc hC hCr (hCc ▸ hv)

omit S in
/-- **The commit argument, stated once.** A quorum-sized `T` whose
decision-round blocks all certify `L` directly commits it. Both pacing
disciplines end here, one through `certifiesAt_of_synchronisedOn`, the
other through `ReactiveM.certifies`. -/
theorem directCommit_of_certifiesAt
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2))
    (hc : CertifiesAt U T r L) :
    DirectCommit U L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop2 v hv
  rw [mem_creatorsOf]
  exact ⟨C, mem_certificatesAt.mpr ⟨hC, hCr, hc v hv C hC hCc hCr⟩, hCc⟩

omit S in
/-- **L4, at the round level.** A correct block at round `r` is directly
committed, given coverage from `r` and correct blocks at `r+1` and `r+2`.
Stated without `Slots`, since the argument only needs `L` correct-authored,
not a leader. -/
theorem directCommit_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1)) (hpop2 : PopulatedOn U T (r + 2))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T) :
    DirectCommit U L r :=
  directCommit_of_certifiesAt hcard hpop2
    (certifiesAt_of_synchronisedOn hcard hs hRr hpop1 hL hLr hLc)

omit [DecidableEq BlockId] in
/-- A correct leader has a candidate block, once its round is populated.
`Populated` at the leader's own round is needed for nothing else. -/
theorem exists_isLeaderBlock (hpop : PopulatedOn U T (S.slotRound k))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop (S.leader k) hlead
  exact ⟨L, hL, hLr, hLc⟩

/-- **L4.** A slot with a correct leader, whose three rounds are populated and
which sits after synchrony, is directly committed. -/
theorem directCommit_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  obtain ⟨L, hL, hLr, hLc⟩ := exists_isLeaderBlock hpop0 hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    directCommit_of_synchronisedOn hcard hs hR hpop1 hpop2 hL hLr
      (by rw [hLc]; exact hlead)⟩

/-- **L4 at `T := Correct`.** The original statement, recovered. -/
theorem directCommit_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  directCommit_of_leader_mem card_correct hs hR hpop0 hpop1 hpop2 hlead

/-! ### From `DirectCommit` to an actual decision

L4 concludes the universe-level rule; the ledger is defined over `Decided`.
The full view closes the gap, since it holds every certificate there is. -/

omit S in
/-- A universe-level direct commit is one the full view also sees. -/
theorem directCommitIn_full (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r :=
  (HoldsAtLeast.full fun _ hC => (mem_certificatesAt.mp hC).1).mpr h

omit S in
/-- A view caught up to the certificate round sees every certificate, so
a direct commit in the universe is a direct commit in the view. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U}
    (h : DirectCommit U L r) (hcov : V.CoversUpto (r + 2)) :
    DirectCommitIn U V L r :=
  HoldsAtLeast.of_coversUpto
    (fun C hC => ⟨(mem_certificatesAt.mp hC).1, (mem_certificatesAt.mp hC).2.1.le⟩) hcov h

omit S in
/-- **The commit argument at the view level.** Counts `T`'s decision-round
blocks in a view rather than the universe, asking only for `T`'s blocks
at one round rather than the whole layer — which is what lets a
rate-limited validator commit (`Properties/Deliver.lean`). -/
theorem directCommitIn_of_certifiesAt {V : View Validator BlockId Payload U}
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2))
    (hcov : ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = r + 2 → b ∈ V.ids)
    (hc : CertifiesAt U T r L) :
    DirectCommitIn U V L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop2 v hv
  exact mem_heldAuthors.mpr ⟨C, mem_certificatesAt.mpr ⟨hC, hCr, hc v hv C hC hCc hCr⟩,
    hcov C hC (by rw [hCc]; exact hv) hCr, hCc⟩

/-- **L4, as a decision.** What L6 consumes and L3 propagates. -/
theorem decided_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hpop2 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- **L4, against a horizon.** Production is available as a single
hypothesis up to a horizon, and the three rounds L4 needs are read off
it — the form every capstone in report §§6–10 uses. Production is asked
over `T` rather than all of `Correct`, which is what lets the
recurrence results run at a proper subset: correct validators outside
`T` may be starved and the ledger still commits, provided `T` itself is
a quorum. -/
theorem decided_of_leader_of_populated (_hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem hcard hs hR
    (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega))
    (hpop _ (by omega) (by omega)) hlead

/-- The same at `T := Correct`. -/
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem card_correct hs hR hpop0 hpop1 hpop2 hlead

/-! ## L5 — an absent leader is skipped

`Decided.directSkip` asks for a quorum of voting-round
blocks referencing no candidate of the slot; when the leader published
nothing every voting-round block qualifies, so the premise reduces to a
quorum being present at that round. The count cannot be dropped: a
premise quantified over the candidates the universe happens to hold
would be discharged vacuously by a validator holding nothing at all. -/

/-- A populated round, seen by a view that covers it, supplies the count
the skip rule asks for. -/
theorem quorate_of_populatedOn {V : View Validator BlockId Payload U}
    {T : Finset Validator} {r : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T r) (hcov : V.CoversUpto r) :
    quorumCard Validator ≤ (creatorsOf U.block (blocksAt U r ∩ V.ids)).card := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro t ht
  obtain ⟨b, hb, hbc, hbr⟩ := hpop t ht
  refine mem_creatorsOf.mpr ⟨b, ?_, hbc⟩
  exact Finset.mem_inter.mpr ⟨mem_blocksAt.mpr ⟨hb, hbr⟩, hcov b hb (le_of_eq hbr)⟩

/-- L5, in the form the `Decided` constructor wants. -/
theorem decided_none_of_no_candidate {V : View Validator BlockId Payload U}
    (h : ∀ L, ¬ IsLeaderBlock U k L)
    (hq : quorumCard Validator ≤
      (creatorsOf U.block (blocksAt U (S.slotRound k + 1) ∩ V.ids)).card) :
    Decided U V k none :=
  Decided.directSkip (directSkipSlotIn_of_no_candidate h hq)

/-- **L5 — an absent leader is skipped.** If the slot-`k` leader has no block
at its round, every view holding a quorum at the voting round decides
`none`. -/
theorem decided_none_of_leader_absent {V : View Validator BlockId Payload U}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k)
    (hq : quorumCard Validator ≤
      (creatorsOf U.block (blocksAt U (S.slotRound k + 1) ∩ V.ids)).card) :
    Decided U V k none :=
  decided_none_of_no_candidate (fun _ hL => h _ hL.1 hL.2.1 hL.2.2) hq

/-- **A slot every sufficiently grown synchronous execution commits.**
The conclusion the recurrence results share; naming it keeps the
quantifier order visible, the slot fixed by the schedule alone before
any execution is named. Both production and coverage are asked over
the same `T`, a statement about any quorum-sized set of reliable
validators rather than all of `Correct` — correct validators outside
`T` may be permanently starved and the slot still commits. Production
is asked for only from `R` on, which is the range a build-rule
structure can actually supply. -/
def CommitsAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)

/-! ## L6 — commits recur

The statement's quantifier order is its whole content:
fixing the DAG and horizon first would let the horizon cap how far
fairness may reach, since a correct leader's slot could lie past it.
Naming the slot from the schedule alone, before any DAG, avoids this —
"the ledger grows without bound" means no slot is the last one a DAG
can be grown far enough to commit. -/

/-- The all-of-`Correct` case. -/
abbrev FairSchedule : Prop := FairScheduleOn (Correct : Finset Validator)

/-- Per-validator fairness is fairness. -/
theorem FairToEach.fairScheduleOn {T : Finset Validator}
    (h : FairToEach T) (hne : T.Nonempty) : FairScheduleOn T := by
  obtain ⟨v, hv⟩ := hne
  intro k
  obtain ⟨k', hk, hlead⟩ := h v hv k
  exact ⟨k', hk, hlead ▸ hv⟩

omit [Fintype Validator] [DecidableEq Validator] F in
/-! A run of `c` slots spanning eligibility — every slot below the run
having its last slot as an eligible anchor — is `SpansEligible` at the
core: `c = 1` under three-round spacing, `c = 3` under pipelining. -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Some slot sits at or beyond any given round: the `Slots` class field
`unbounded`, in the shape L6 needs to apply fairness past `R`. -/
theorem exists_slotRound_ge (n : ℕ) : ∃ k, n ≤ S.slotRound k := S.unbounded n

variable (Validator) in
omit [Fintype Validator] [DecidableEq Validator] F in
omit [Fintype Validator] [DecidableEq Validator] F in
omit [Fintype Validator] [DecidableEq Validator] F in
/-! **Every slot has an eligible anchor somewhere** — the relation's
`exists_eligible`, from `unbounded`: the restriction to slots past `k`'s
decision round would be worthless if no such slot existed. -/

/-- **L6 — commits recur.** For every slot `k` there is a later slot `k'`
that every sufficiently grown synchronous DAG commits, the slot fixed
by the schedule alone before the DAG is named. -/
theorem commits_recur_on (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload T R k' := by
  -- Some slot `k₀` already sits past round `R` (`unbounded`), and every slot
  -- from `k₀` on sits at least as late (`mono`). That is all this needs; the
  -- old proof got the same from `3 * k ≤ slotRound k`, which a pipelined or
  -- multi-leader schedule does not satisfy.
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨k', hk', hlead⟩ := fair (max k k₀)
  have hRk' : R ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hk'))
  refine ⟨k', le_trans (le_max_left _ _) hk', hRk', ?_⟩
  intro U N hpop hs hN
  -- L1 populates all of `Correct`; `T` is a subset, so `.mono` bridges them.
  -- This is the one place `T ⊆ Correct` is genuinely needed: L4 alone cares
  -- only about `T.card`, but its population has to come from somewhere, and
  -- the only source is L1, which knows about correct validators.
  exact decided_of_leader_of_populated hT hcard hs hRk' hpop (by omega) hlead

/-- **L6 at `T := Correct`.** The original statement, recovered. -/
theorem commits_recur (fair : FairSchedule (Validator := Validator)) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload (Correct : Finset Validator) R k' :=
  commits_recur_on Finset.Subset.rfl card_correct fair R k

/-! ## L8 — no undecided slot below a commit

L6 says commits recur; it does not say every slot is decided, and the
difference matters because `commitSeq` reads verdicts in slot order, so
one permanently undecided slot withholds delivery of everything above
it (the Mysticeti paper's backpressure, §III-C). The theorem below
clears it under `helig`, every later slot an eligible anchor — the old
three-round spacing, which pipelining destroys. The conclusion survives
pipelining anyway: slot `j - 1` cannot anchor on `j`, but can anchor on
`j + 2` with a vacuous intermediate premise, so the escape needs no
induction (`decided_of_first_eligible_commit`). `helig` fails only when
commits are isolated with no three consecutive, which fair round-robin
excludes and L9 makes precise. -/

/-- **The escape.** If `j` is committed and nothing strictly between `k`
and `j` is eligible to anchor `k`, then `k` is decided outright: the
intermediate-skip premise is vacuous. This is what keeps pipelining
live — slot `j - 1` cannot anchor on `j` but can anchor on `j + 2` with
an empty intermediate range, and fair leader election commits `j + 2`
whenever `j` is committed. -/
theorem decided_of_first_eligible_commit {V : View Validator BlockId Payload U}
    {k j : ℕ} {A : BlockId}
    (helig : (coreAnchored Validator BlockId Payload).Eligible k j)
    (hfirst : ∀ i, k < i → i < j → ¬ (coreAnchored Validator BlockId Payload).Eligible k i)
    (hj : Decided U V j (some A)) :
    ∃ v, Decided U V k v := by
  classical
  have hmid : ∀ i, k < i → i < j → (coreAnchored Validator BlockId Payload).Eligible k i →
      Decided U V i none :=
    fun i h1 h2 h3 => absurd h3 (hfirst i h1 h2)
  by_cases hc : ∃ L, IsLeaderBlock U k L ∧ CertifiedIn U A L (S.slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    exact ⟨some L, AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h)
      (AnchoredRule.lt_of_eligible _ helig) helig hj hmid hL hcert⟩
  · push Not at hc
    exact ⟨none, AnchoredRule.Decided.indirectSkip_single rfl
      (AnchoredRule.lt_of_eligible _ helig) helig hj hmid
      (fun L hL ⟨C, hC, hre⟩ => hc L hL C hC hre)⟩

open Classical in
/-- **L8.** Given a committed slot, every slot below it is decided,
provided every later slot may anchor an earlier one — pure
decision-relation combinatorics, with no synchrony, timing or fairness.
The work is choosing the nearest committed slot above `i` and reading
the intermediate premise off the induction hypothesis. -/
theorem decided_of_committed_above
    (helig : ∀ a b : ℕ, a < b → (coreAnchored Validator BlockId Payload).Eligible a b)
    {V : View Validator BlockId Payload U} {n : ℕ} {A : BlockId}
    (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → ∃ v, Decided U V i v := by
  classical
  have key : ∀ d i, i ≤ n → n - i ≤ d → ∃ v, Decided U V i v := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      exact ⟨some A, (by omega : i = n) ▸ hn⟩
    | succ d ih =>
      intro i hi hd
      rcases eq_or_lt_of_le hi with heq | hlt
      · exact ⟨some A, heq ▸ hn⟩
      -- The nearest committed slot strictly above `i`, which exists since `n`
      -- is one. `Nat.find` needs classical decidability: `Decided` is a Prop.
      have hex : ∃ j, i < j ∧ j ≤ n ∧ ∃ A', Decided U V j (some A') :=
        ⟨n, hlt, le_refl _, A, hn⟩
      obtain ⟨hij, hjn, A', hA'⟩ := Nat.find_spec hex
      -- Every slot between is decided by induction, and `none` by nearestness.
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          (coreAnchored Validator BlockId Payload).Eligible i i' → Decided U V i' none := by
        intro i' h1 h2 _
        have hi'n : i' ≤ n := by omega
        obtain ⟨v, hv⟩ := ih i' hi'n (by omega)
        cases v with
        | none => exact hv
        | some B => exact absurd ⟨h1, hi'n, B, hv⟩ (Nat.find_min hex h2)
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U A' L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        exact ⟨some L, AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) hij
          (helig i _ hij) hA' hmid hL hcert⟩
      · push Not at hc
        exact ⟨none, AnchoredRule.Decided.indirectSkip_single rfl hij (helig i _ hij) hA' hmid
          (fun L hL ⟨C, hC, hre⟩ => hc L hL C hC hre)⟩
  intro i hi
  exact key (n - i) i hi (le_refl _)

/-- **L8 under three-round spacing.** Combining L6 with L8: for every
slot `k` there is a slot `n ≥ k` such that a sufficiently grown
synchronous DAG decides every slot up to `n`. A pipelined or
multi-leader schedule does not satisfy `hsp`, which is why this is
stated conditionally. -/
theorem all_decided_below_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ n, k ≤ n ∧ R ≤ S.slotRound n ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound n + 2 ≤ N →
        ∀ i, i ≤ n → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨n, hkn, hRn, hcommit⟩ := commits_recur_on (BlockId := BlockId) (Payload := Payload)
    hT hcard fair R k
  refine ⟨n, hkn, hRn, ?_⟩
  intro U N hpop hs hN
  obtain ⟨L, _, hdec⟩ := hcommit U N hpop hs hN
  exact decided_of_committed_above (fun _ _ h => eligibleAt_of_lt_of_spacing hsp h) hdec

/-! ## L9 — the obstruction: when slots are stuck for good

The converse of L8, and the reason `helig` is a hypothesis rather than
dropped: a set of slots that is stuck stays stuck. `X` is stuck when no
slot in it has a certificate anywhere, some candidate is not directly
skippable, and every committed eligible anchor has another member of
`X` eligibly between it and the slot. That third clause requires
commits to be isolated with no three consecutive — impossible under
three-round spacing, and excluded by fair round-robin under
pipelining, since it needs Byzantine leaders holding roughly three of
every four consecutive slots. -/

/-- **L9.** Nothing in a stuck set is ever decided, on any view: by
induction on the derivation, three of the four cases die immediately
(commits produce a certificate; a direct skip contradicts the
unskippable candidate), and the fourth, indirect skip, regresses to a
sub-derivation the stuck clause places back inside `X`. -/
theorem notMem_stuck_of_decided {V : View Validator BlockId Payload U} {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, (coreAnchored Validator BlockId Payload).Eligible i j →
      (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ (coreAnchored Validator BlockId Payload).Eligible i i')
    {i : ℕ} {v : Option BlockId} (h : Decided U V i v) : i ∉ X := by
  induction h with
  | @directCommit k L hL hdc =>
    intro hk
    obtain ⟨C, hC⟩ := certificates_nonempty_of_directCommit (directCommit_of_directCommitIn hdc)
    rw [hcert k hk L hL] at hC
    exact absurd hC (Finset.notMem_empty C)
  | @directSkip k hall =>
    intro hk
    obtain ⟨L, hL, hns⟩ := hskip k hk
    exact hns (directSkipIn_of_directSkipSlotIn hall hL)
  | @indirectCommit k j A L i _ _ _ _ _ _ hL hcertIn _ _ _ =>
    intro hk
    obtain ⟨C, hC⟩ := certificates_nonempty_of_certifiedIn hcertIn
    rw [hcert k hk L hL] at hC
    exact absurd hC (Finset.notMem_empty C)
  | @indirectSkip k j A _ helig hj _ _ _ ihmid =>
    intro hk
    obtain ⟨i', hi'X, h1, h2, h3⟩ := hregress k hk j helig ⟨A, hj⟩
    exact ihmid i' h1 h2 h3 hi'X

/-! **P7′ — a committed run decides everything below it** — is the
relation's `decided_below_of_committed_run` at `exists_least`: L8 with
`helig` removed. Given slots `b … n` committed and every slot below `b`
having `n` as an eligible anchor — under pipelining, that the run spans
three rounds — every slot below `b` is decided, with no synchrony,
timing, fairness or schedule hypothesis. -/

/-- **L8 and L9 are consistent, and their hypotheses are jointly
exhaustive.** Under three-round spacing a stuck set has no member below
a committed slot: L8 decides the slot, L9 says a decided slot is
outside `X`, and neither theorem is vacuous — L9's hypotheses are
unsatisfiable only under `helig`. -/
theorem stuck_empty_below_commit_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    {V : View Validator BlockId Payload U} {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, (coreAnchored Validator BlockId Payload).Eligible i j →
      (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ (coreAnchored Validator BlockId Payload).Eligible i i')
    {n : ℕ} {A : BlockId} (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → i ∉ X := by
  intro i hi
  obtain ⟨v, hv⟩ :=
    decided_of_committed_above (fun _ _ h => eligibleAt_of_lt_of_spacing hsp h) hn i hi
  exact notMem_stuck_of_decided hcert hskip hregress hv

end LeanDag
