import LeanDag.OptimalHydrozoan.SlotAgreement.Proof
import LeanDag.OptimalHydrozoan.Helpers.Banded
import LeanDag.OptimalHydrozoan.Helpers.Decided
import LeanDag.Common.Anchored.Band
import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.OptimalHydrozoan.DirectLiveness.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# Optimal-Hydrozoan as a carrier, and the three properties its rules give

`docs/porting-plan.md` step 3. The carrier and the properties whose
proof is a single Optimal theorem apiece.

**The universe is the record under the schedule-free exclusion.**
`OptUniverse` is *indexed by the schedule*: its `leader_excluded` field
reads `S.leader k` and `LeanDag.Hydrozoan.decisionRound k`, so `OptUniverse` at `S` and at
`S'` are different types, while `DagRule.Universe` is one type and
`Properties.Banded` compares verdicts across schedules. The carrier's
universes are therefore the records satisfying `LeaderExcludedAll`, the
same exclusion quantified over rounds and validators rather than over
slots, hence schedule-free; `leaderExcluded_of_all` supplies exclusion
at whatever schedule a property names, which is what the relation's
laws hold under. The carrier is the relation's `toDagRuleOn` at that
invariant, exactly as Hybrid's is at `HonestNoEquiv`.
-/

namespace LeanDag

namespace OptimalHydrozoanProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan as a carrier**: the anchored relation's, on the
records under the schedule-free exclusion. -/
abbrev optimalRule : DagRule Replica BlockId Unit :=
  (LeanDag.OptimalHydrozoan.optimalAnchored Replica BlockId).toDagRuleOn
    LeanDag.OptimalHydrozoan.LeaderExcludedAll

/-- **Optimal-Hydrozoan's universes are quorate.** The underlying
universe is Hydrozoan's, so the clause and the fault model are
Hydrozoan's. -/
theorem quorate : Quorate (optimalRule (Replica := Replica) (BlockId := BlockId))
    (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro U b hb hr
  have h := (U.val.valid b hb).quorum hr
  have hq : LeanDag.Hydrozoan.q Replica
      = Fintype.card Replica - (LeanDag.Hydrozoan.hzReliability Replica).slack := by
    show LeanDag.Hydrozoan.q Replica = Fintype.card Replica - (_ + _)
    unfold LeanDag.Hydrozoan.q; omega
  rw [hq] at h
  exact h

/-- **Two views decide alike.** OH5 under the property's name: the
relation's agreement at Optimal's laws, the carrier's schedule-free
exclusion supplying exclusion at every schedule. -/
theorem agree : Agree (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.agreeOn LeanDag.OptimalHydrozoan.SlotAgreement.optimalLaws
    (fun S U h => LeanDag.OptimalHydrozoan.leaderExcluded_of_all (S := S) U h)

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate :
    CommitsCandidate (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.commitsCandidateOn

/-- **And a direct commit is a verdict**, at Optimal's own direct
predicate — a *disjunction*, the fast path or the slow one. -/
theorem commitsDirect :
    CommitsDirect (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun {U} V L r => LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L r ∨
        LeanDag.Hydrozoan.SlowCommitInView U.val V L r) :=
  AnchoredRule.commitsDirectOn

/-! ## The band -/

/-- **Optimal-Hydrozoan reads a band**: the relation's band at its band
laws, which are Hydrozoan's direct layer and rung `0` and Optimal's fast
path and evidence rung. -/
theorem banded : Banded (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.bandedOn LeanDag.OptimalHydrozoan.optimalBandLaws

/-! ## The two liveness properties

`Descends` is not among them: it follows from `Indirect` by the generic
induction of `Properties/Derived/Descent.lean`. -/

/-- **Optimal-Hydrozoan's liveness precondition**, over a slot window.
Hydrozoan's, unchanged: the slow path is the one that carries the
guarantee, and Optimal leaves it alone — the fast path is about
latency, not liveness. -/
def optLive (S : LeanDag.Slots Replica)
    {U : (optimalRule (Replica := Replica) (BlockId := BlockId)).Universe}
    (V : LeanDag.Hydrozoan.View U.val) (T : Finset Replica) (lo K : ℕ) : Prop :=
  T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) ∧
    LeanDag.Hydrozoan.q Replica ≤ T.card ∧
    ∃ R₀ N, SynchronisedOn U.val T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U.val T r) ∧
      V.CoversUpto N ∧
      ∀ k, k < K → S.slotRound k + 2 ≤ N

/-! ## Optimal-Hydrozoan's support shape

Hydrozoan's, at the underlying universe: Optimal changes the fast path
and the skip, and the slow path is what liveness runs on. Laws 1 and 2
are Hydrozoan's applied — the carrier projects to the same blocks — and
Law 3 is Hydrozoan's slow commit wrapped in `DecidedOpt`. -/

/-- **Optimal-Hydrozoan's support.** -/
def optSupport : Support (optimalRule (Replica := Replica) (BlockId := BlockId)) where
  wave := 2
  Certifies := fun U C L => LeanDag.Hydrozoan.IsCertificate U.val C L

/-- **Law 1**, Hydrozoan's at the underlying universe. -/
theorem optSupport_local [LinearOrder BlockId] :
    Support.Local (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport := by
  intro U U' G R₀ h c L hc hcr hL hLr
  exact LeanDag.Hydrozoan.hzSupport_local (U := U.val) (U' := U'.val)
    ⟨h.mem, h.round, h.creator, h.refs⟩ c L hc hcr hL hLr

/-- **Law 2**, Hydrozoan's at the underlying universe. -/
theorem optSupport_ofCoverage :
    Timed.OfCoverage (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro U T hq r L hpop hct hL hLr hLc c hc hcc hcr
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  exact LeanDag.Hydrozoan.isCertificate_of_coversToward hcard
    (hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega)) hct hL hLr hLc hc hcc hcr

/-- **Law 3**: the slow commit, in `DecidedOpt`. -/
theorem optSupport_commits :
    Support.Commits (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hL : LeanDag.IsLeaderBlock U.val k L := ⟨hLmem, hLr, hLc⟩
  have hslow : LeanDag.Hydrozoan.SlowCommit U.val L (S.slotRound k) :=
    LeanDag.Hydrozoan.slowCommit_of_certifiesAt hcard
      (hpop (S.slotRound k + 2) (by omega) (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega))
      (hcert L ⟨hLmem, hLr, hLc⟩)
  have hin : LeanDag.Hydrozoan.SlowCommitInView U.val V L (S.slotRound k) :=
    LeanDag.Hydrozoan.slowCommitInView_of_coversUpto hslow hcov
  refine ⟨L, by omega, LeanDag.OptimalHydrozoan.DecidedOpt.directCommit hL (Or.inr hin), ?_⟩
  intro S' hround hlead'
  refine LeanDag.OptimalHydrozoan.DecidedOpt.directCommit
    (S := S') ⟨hL.1, ?_, ?_⟩ (Or.inr ?_)
  · change (U.val.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.val.block L).creator = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.SlowCommitInView U.val V L (S'.slotRound k)
    rw [hround]; exact hin

/-- **Optimal-Hydrozoan's precondition is the support's.** -/
theorem optSupport_live_of_optLive {S : LeanDag.Slots Replica}
    {U : (optimalRule (Replica := Replica) (BlockId := BlockId)).Universe}
    {V : LeanDag.Hydrozoan.View U.val} {T : Finset Replica} {lo K : ℕ}
    (h : optLive S (U := U) V T lo K) :
    Support.live (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) S (U := U) V T lo K := by
  obtain ⟨hT, hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := h
  have hq : (LeanDag.Hydrozoan.hzReliability Replica).IsQuorum T := ⟨hT, by
    change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card
    unfold LeanDag.Hydrozoan.q at hcard; omega⟩
  have hpop' : ∀ n, R₀ ≤ n → n ≤ N →
      Properties.PopulatedOn (optimalRule (Replica := Replica) (BlockId := BlockId)) U T n := by
    intro n h1 h2 v hv
    obtain ⟨b, hb, hba, hbr⟩ := hpop n h1 h2 v hv
    exact ⟨b, hb, hba, hbr⟩
  refine ⟨hq, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  refine ⟨fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩ v hv c hc hcc hcr
  exact optSupport_ofCoverage U T hq (S.slotRound k) L
    (fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega))
    (Timed.coversToward_of_synchronisedOn hs hRk) hLmem hLr (by rw [hLc]; exact hlead)
    c hc (by rw [hcc]; exact hv) hcr

/-- **A reliably-led slot commits**, now a corollary of the support. -/
theorem leaderCommits :
    LeaderCommits (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun S {U} V T lo K => optLive S (U := U) V T lo K) :=
  fun S _ V T lo K h =>
    Support.leaderCommits optSupport optSupport_commits S V T lo K (optSupport_live_of_optLive h)

/-! ## Optimal-Hydrozoan's fast path

`voteSupport` again — one round up, certifying is referencing — at the
optimised threshold `q_fast = n − pOpt`, under a fault model with at
most `pOpt` faults of either kind. -/

/-- **The fast path's fault model.** `pOpt` faults is a minority at every
committee but the degenerate corner `f = 0`, `c = 1`, `k` odd, where
`2·pOpt = n` exactly; the committee equation does not exclude it, so
strict minority is a hypothesis rather than a consequence. -/
def optFastReliability (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]
    (h : (O.byzantine ∪ O.crashed).card ≤ LeanDag.OptimalHydrozoan.pOpt Replica)
    (hmin : 2 * LeanDag.OptimalHydrozoan.pOpt Replica < Fintype.card Replica) :
    LeanDag.Reliability Replica where
  correct := (LeanDag.Hydrozoan.Correct : Finset Replica)
  slack := LeanDag.OptimalHydrozoan.pOpt Replica
  covers := by
    have hc : (LeanDag.Hydrozoan.Correct : Finset Replica)ᶜ = O.byzantine ∪ O.crashed := by
      simp [LeanDag.Hydrozoan.Correct]
    rw [hc]; exact h
  minority := hmin

/-- **Law 3 of `voteSupport`, for Optimal-Hydrozoan's fast path.** -/
theorem voteSupport_fast_commits
    (h : (O.byzantine ∪ O.crashed).card ≤ LeanDag.OptimalHydrozoan.pOpt Replica)
    (hmin : 2 * LeanDag.OptimalHydrozoan.pOpt Replica < Fintype.card Replica) :
    Support.Commits (R := optimalRule (Replica := Replica) (BlockId := BlockId))
      (voteSupport (optimalRule (Replica := Replica) (BlockId := BlockId)))
      (optFastReliability Replica h hmin) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.OptimalHydrozoan.qFastOpt Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - LeanDag.OptimalHydrozoan.pOpt Replica ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hL : LeanDag.IsLeaderBlock U.val k L := ⟨hLmem, hLr, hLc⟩
  have hfast : LeanDag.OptimalHydrozoan.FastCommitOpt U.val L (S.slotRound k) := by
    have hsub : T ⊆ supporters U.val L (S.slotRound k + 1) := by
      intro v hv
      obtain ⟨b, hb, hba, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) v hv
      exact mem_supporters.mpr
        ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hba hbr, hba⟩
    exact le_trans hcard (Finset.card_le_card hsub)
  have hin : LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L (S.slotRound k) :=
    HoldsAtLeast.of_coversUpto
      (fun b hb => ⟨(mem_votesFor.mp hb).1, (mem_votesFor.mp hb).2.1.le⟩) hcov hfast
  refine ⟨L, by omega, LeanDag.OptimalHydrozoan.DecidedOpt.directCommit hL (Or.inl hin), ?_⟩
  intro S' hround hlead'
  refine LeanDag.OptimalHydrozoan.DecidedOpt.directCommit
    (S := S') ⟨hL.1, ?_, ?_⟩ (Or.inl ?_)
  · change (U.val.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.val.block L).creator = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L (S'.slotRound k)
    rw [hround]; exact hin

/-- **The graded rule is total, at a bound**: the relation's indirect
property at the rule's rung choices, read at the three-round
eligibility. Every clause reads slot `k`'s own candidates and the
anchor's history, and none moves when the leaders of other slots are
reassigned — the relation's `link_congr`. -/
theorem indirect :
    Indirect (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun sr i j => sr i + 3 ≤ sr j) :=
  (AnchoredRule.indirectOn LeanDag.OptimalHydrozoan.SlotAgreement.optimalLaws.link_congr
    fun hi h => LeanDag.OptimalHydrozoan.exists_least hi h).congr
    (fun _ _ _ => by simp only [LeanDag.OptimalHydrozoan.optimalAnchored_wave])

/-! ## The headlines -/

theorem safety :
    Properties.Safe (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  Properties.safety banded agree commitsCandidate

theorem progress : Properties.Support.Progresses
    (optSupport (Replica := Replica) (BlockId := BlockId)) (LeanDag.Hydrozoan.hzReliability Replica) :=
  Properties.Support.progress optSupport_commits

end OptimalHydrozoanProperties

end LeanDag
