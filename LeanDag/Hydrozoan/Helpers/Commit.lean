import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.IndirectLiveness
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Candidate
import LeanDag.Properties.Deliver
import LeanDag.Timed.Coverage
/-!
# Hydrozoan's liveness obligations

`docs/target-properties.md` §4. `Agree`, `LeaderCommits` and `Descends`
for this protocol, each resting on an arc result that was already
proved: slot agreement, direct liveness, and the graded rule's totality
with the committed-run descent.

What has to be added is the **bound**. `DecidedBelow` records that a
verdict survives any reassignment of the leaders at or above a slot
bound, and an opaque `Decided` cannot supply that, so each verdict is
rebuilt here from the constructor the arc result hands over: the slow
commit for a reliable leader, and the graded trichotomy for a slot under
an anchor. Both read the schedule only at the slot they decide, which is
what makes the bound tight.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- **Slot agreement as a property.** -/
theorem agree : Agree (rule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.agree SlotAgreement.hydrozoanLaws

/-- **Hydrozoan's liveness precondition**, over a slot window: a correct
DAG quorum synchronised from a round at or below the window's first
slot, filling every round to a horizon the view is caught up to, with
every slot of the window two rounds under it. It names no leader, so it
holds under every schedule with the same rounds. -/
def hzLive (S : LeanDag.Slots Replica) {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (V : LeanDag.Hydrozoan.View U) (T : Finset Replica) (lo K : ℕ) : Prop :=
  T ⊆ (Correct : Finset Replica) ∧ LeanDag.Hydrozoan.q Replica ≤ T.card ∧
    ∃ R₀ N, SynchronisedOn U T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) ∧
      V.CoversUpto N ∧
      ∀ k, k < K → S.slotRound k + 2 ≤ N

/-! ## Hydrozoan's support shape

`Properties/Support.lean`. The slow path: certificates two rounds above
the candidate, each a block whose voting refs number `q_cert`. The
fast path is latency and is not a liveness shape. -/

omit [LinearOrder BlockId] in
/-- **A quorum's certificates are a slow commit.** The certificate half
of `slowCommit_of_synchronised`, with the coverage argument factored
out so that Optimal-Hydrozoan can take it at its own universe. -/
theorem slowCommit_of_certifiesAt {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {T : Finset Replica} {r : ℕ} {L : BlockId}
    (hcard : LeanDag.Hydrozoan.q Replica ≤ T.card)
    (hpop2 : ∀ v ∈ T, ∃ C ∈ U.ids, (U.block C).creator = v ∧ (U.block C).round = r + 2)
    (hcert : ∀ v ∈ T, ∀ C, C ∈ U.ids → (U.block C).creator = v → (U.block C).round = r + 2 →
      LeanDag.Hydrozoan.IsCertificate U C L) :
    LeanDag.Hydrozoan.SlowCommit U L r := by
  have hsub : T ⊆ LeanDag.Hydrozoan.certifiers U L r := by
    intro v hv
    obtain ⟨C, hC, hCa, hCr⟩ := hpop2 v hv
    exact LeanDag.mem_creatorsOf.mpr
      ⟨C, mem_certificatesAt.mpr ⟨hC, hCr, hcert v hv C hC hCa hCr⟩, hCa⟩
  exact le_trans LeanDag.Hydrozoan.qSlow_le_q (le_trans hcard (Finset.card_le_card hsub))

/-- **Hydrozoan's support**: wavelength two, certification the rule's own. -/
def hzSupport : Support (rule (Replica := Replica) (BlockId := BlockId)) where
  wave := 2
  Certifies := fun U C L => LeanDag.Hydrozoan.IsCertificate U C L

/-- **Law 1.** A certifier two rounds above the settling round keeps its
refs, and each parent keeps its refs and its creator. -/
theorem hzSupport_local :
    Support.Local (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport := by
  intro U U' G R₀ h c L hc hcr _ _
  change R₀ + 2 ≤ (U.block c).round at hcr
  have hrefs : (U'.block c).refs = (U.block c).refs :=
    h.refs c hc (by change R₀ < (U.block c).round; omega)
  have hpar : ∀ b ∈ (U.block c).refs,
      (U'.block b).refs = (U.block b).refs ∧ (U'.block b).creator = (U.block b).creator := by
    intro b hb
    have hbU := U.complete c hc b hb
    have hbr := (U.valid c hc).predecessor b hb
    exact ⟨h.refs b hbU (by change R₀ < (U.block b).round; omega),
      h.creator b hbU (by change R₀ ≤ (U.block b).round; omega)⟩
  change LeanDag.Hydrozoan.IsCertificate U' c L ↔ LeanDag.Hydrozoan.IsCertificate U c L
  unfold LeanDag.Hydrozoan.IsCertificate CarriesVotes carriedVotes LeanDag.creatorsOf
  rw [hrefs, Finset.filter_congr (fun b hb => by
      unfold IsVote; rw [(hpar b hb).1]),
    Finset.image_congr (fun b hb => (hpar b (Finset.mem_of_mem_filter b hb)).2)]

/-- **Law 2.** Coverage toward the candidate over two layers makes every
quorum block two rounds up a certificate: `isCertificate_of_synchronised`
with its antecedent cut to what it reads. -/
theorem hzSupport_ofCoverage :
    Timed.OfCoverage (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) := by
  intro U T hq r L hpop hct hL hLr hLc C hC hCc hCr
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  exact isCertificate_of_coversToward hcard
    (hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega)) hct hL hLr hLc hC hCc hCr

/-- **Law 3.** A quorum's certificates at the slot's candidate are a
slow commit, which a view caught up to the decision round sees. -/
theorem hzSupport_commits :
    Support.Commits (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hL : LeanDag.IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hslow : LeanDag.Hydrozoan.SlowCommit U L (S.slotRound k) :=
    slowCommit_of_certifiesAt hcard
      (hpop (S.slotRound k + 2) (by omega) (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega))
      (hcert L ⟨hLmem, hLr, hLc⟩)
  have hin : LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound k) :=
    slowCommitInView_of_coversUpto hslow hcov
  refine ⟨L, by omega, LeanDag.Hydrozoan.Decided.directCommit hL (Or.inr hin), ?_⟩
  intro S' hround hlead'
  refine LeanDag.Hydrozoan.Decided.directCommit (S := S') ⟨hL.1, ?_, ?_⟩ (Or.inr ?_)
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).creator = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.SlowCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin

/-- **Hydrozoan's precondition is the support's.** Coverage from `R₀`
is coverage toward every candidate, and the quorum is inside the
correct set, so `hzLive` is `Support.live` at every slot of the window. -/
theorem hzSupport_live_of_hzLive {S : LeanDag.Slots Replica}
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {V : LeanDag.Hydrozoan.View U}
    {T : Finset Replica} {lo K : ℕ} (h : hzLive S (U := U) V T lo K) :
    Support.live (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) S (U := U) V T lo K := by
  obtain ⟨hT, hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := h
  have hq : (hzReliability Replica).IsQuorum T := ⟨hT, by
    change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card
    unfold LeanDag.Hydrozoan.q at hcard; omega⟩
  have hpop' : ∀ n, R₀ ≤ n → n ≤ N →
      Properties.PopulatedOn (rule (Replica := Replica) (BlockId := BlockId)) U T n := by
    intro n h1 h2 v hv
    obtain ⟨b, hb, hba, hbr⟩ := hpop n h1 h2 v hv
    exact ⟨b, hb, hba, hbr⟩
  refine ⟨hq, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  refine ⟨fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩ v hv c hc hcc hcr
  exact hzSupport_ofCoverage U T hq (S.slotRound k) L
    (fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega))
    (Timed.coversToward_of_synchronisedOn hs hRk) hLmem hLr (by rw [hLc]; exact hlead)
    c hc (by rw [hcc]; exact hv) hcr

/-- **Direct liveness as a property**, now a corollary: the bridge
composed with the one `LeaderCommits` every support has. -/
theorem leaderCommits :
    LeaderCommits (rule (Replica := Replica) (BlockId := BlockId))
      (fun S {U} V T lo K => hzLive S (U := U) V T lo K) :=
  fun S _ V T lo K h =>
    Support.leaderCommits hzSupport hzSupport_commits S V T lo K (hzSupport_live_of_hzLive h)

/-! ## Hydrozoan's fast path

A second `Support` for the same rule, which is what the parameter form
is for. The fast path is `voteSupport`: one round up, certifying is
referencing, so Laws 1 and 2 are the generic ones. What it costs is the
fault model: `q_fast = n − p` votes, and a reliable set that large exists
only when at most `p` replicas are faulty. `hzFastReliability` is that
model, and Law 3 holds under it. -/

/-- **The fast path's fault model**: at most `p` replicas Byzantine or
crashed, so the correct set carries `q_fast`. -/
def hzFastReliability (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [F : LeanDag.Hydrozoan.Faults Replica]
    (h : (F.byzantine ∪ F.crashed).card ≤ LeanDag.Hydrozoan.p Replica) :
    LeanDag.Reliability Replica where
  correct := (LeanDag.Hydrozoan.Correct : Finset Replica)
  slack := LeanDag.Hydrozoan.p Replica
  covers := by
    have hc : (LeanDag.Hydrozoan.Correct : Finset Replica)ᶜ = F.byzantine ∪ F.crashed := by
      simp [LeanDag.Hydrozoan.Correct]
    rw [hc]; exact h
  minority := by
    have := F.card_replicas
    unfold LeanDag.Hydrozoan.p; omega

omit [LinearOrder BlockId] in
/-- A view caught up to the voting round holds every vote, so a fast
commit in the universe is a fast commit in that view. -/
theorem fastCommitInView_of_coversUpto {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {V : LeanDag.Hydrozoan.View U} {L : BlockId} {r : ℕ}
    (h : LeanDag.Hydrozoan.FastCommit U L r) (hcov : V.CoversUpto (r + 1)) :
    LeanDag.Hydrozoan.FastCommitInView U V L r :=
  HoldsAtLeast.of_coversUpto
    (fun b hb => ⟨(mem_votesFor.mp hb).1, (mem_votesFor.mp hb).2.1.le⟩) hcov h

/-- **Law 3 of `voteSupport`, for Hydrozoan's fast path**, under the fast
fault model: `q_fast` votes one round up are a fast commit, and a view
caught up to the voting round sees it. -/
theorem voteSupport_fast_commits
    (h : (LeanDag.Hydrozoan.Faults.byzantine ∪ LeanDag.Hydrozoan.Faults.crashed :
      Finset Replica).card ≤ LeanDag.Hydrozoan.p Replica) :
    Support.Commits (R := rule (Replica := Replica) (BlockId := BlockId))
      (voteSupport (rule (Replica := Replica) (BlockId := BlockId)))
      (hzFastReliability Replica h) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.Hydrozoan.qFast Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - LeanDag.Hydrozoan.p Replica ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hL : LeanDag.IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hfast : LeanDag.Hydrozoan.FastCommit U L (S.slotRound k) := by
    have hsub : T ⊆ supporters U L (S.slotRound k + 1) := by
      intro v hv
      obtain ⟨b, hb, hba, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) v hv
      exact mem_supporters.mpr
        ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hba hbr, hba⟩
    exact le_trans hcard (Finset.card_le_card hsub)
  have hin : LeanDag.Hydrozoan.FastCommitInView U V L (S.slotRound k) :=
    fastCommitInView_of_coversUpto hfast hcov
  refine ⟨L, by omega, LeanDag.Hydrozoan.Decided.directCommit hL (Or.inl hin), ?_⟩
  intro S' hround hlead'
  refine LeanDag.Hydrozoan.Decided.directCommit (S := S') ⟨hL.1, ?_, ?_⟩ (Or.inl ?_)
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).creator = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.FastCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin



/-! ## The descent -/

/-- **HZ6 as a property.** The relation's indirect property at the
graded rule's rung choices, read at the three-round eligibility. -/
theorem indirect :
    Indirect (rule (Replica := Replica) (BlockId := BlockId))
      (fun sr i j => sr i + 3 ≤ sr j) :=
  (AnchoredRule.indirect SlotAgreement.hydrozoanLaws.link_congr fun hi h => exists_least hi h).congr
    (fun _ _ _ => by simp only [hydrozoanAnchored_wave])

/-- **Hydrozoan has the descent laws** at the hybrid fault model's slack. -/
theorem descent :
    Properties.Descent (rule (Replica := Replica) (BlockId := BlockId))
      (Timed.Good (rule (Replica := Replica) (BlockId := BlockId)) (hzReliability Replica))
      3 (hzReliability Replica).slack :=
  Timed.descent_of_support _ _ 3 hzSupport hzSupport_ofCoverage hzSupport_commits
    indirect (by change 2 ≤ 3; omega) fun _ _ _ h => h

/-- **The descent as a property.** Was two lemmas — the graded rule at a
bound and a downward induction over the run; both are now
`Descends.of_indirect`. -/
theorem descends {S : LeanDag.Slots Replica} {c : ℕ} (hc : 0 < c)
    (hspans : (hydrozoanAnchored Replica BlockId).SpansEligible (S := S) c) :
    Descends (rule (Replica := Replica) (BlockId := BlockId)) S c :=
  Descends.of_indirect indirect hc (fun b i hi => by
    have := (hydrozoanAnchored Replica BlockId).eligible_iff.mp (hspans b i hi)
    simp only [hydrozoanAnchored_wave] at this
    omega)

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate :
    CommitsCandidate (rule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.commitsCandidate

/-- **A direct commit is a verdict**, at Hydrozoan's own direct
predicate — which is a *disjunction*, the fast path or the slow one. -/
theorem commitsDirect :
    Properties.CommitsDirect (rule (Replica := Replica) (BlockId := BlockId))
      (fun {U} V L r => LeanDag.Hydrozoan.FastCommitInView U V L r ∨
        LeanDag.Hydrozoan.SlowCommitInView U V L r) :=
  AnchoredRule.commitsDirect

/-- The carrier's coverage predicate is Hydrozoan's. -/
theorem coversUpto_eq {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {V : LeanDag.Hydrozoan.View U} {N : ℕ} :
    Properties.CoversUpto (rule (Replica := Replica) (BlockId := BlockId)) V N ↔
      V.CoversUpto N := Iff.rfl

/-- **A caught-up replica reaches every verdict**, at the band's own
ceiling rather than a rule-specific round. What a view-level mechanism
has to deliver, for this protocol. -/
theorem exists_coversUpto_decides {S : LeanDag.Slots Replica}
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {W : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId}
    (hW : LeanDag.Hydrozoan.Decided (S := S) U W k v) :
    ∃ N, ∀ V : LeanDag.Hydrozoan.View U, V.CoversUpto N →
      LeanDag.Hydrozoan.Decided (S := S) U V k v :=
  Properties.exists_coversUpto_decides banded (S := S) hW

end Hydrozoan

end LeanDag
