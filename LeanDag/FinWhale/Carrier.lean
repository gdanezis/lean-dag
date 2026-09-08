import LeanDag.FinWhale.View
import LeanDag.FinWhale.Band
import LeanDag.FinWhale.Least
import LeanDag.FinWhale.Procedure.Pass
import LeanDag.Common.Anchored.Band
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
/-!
# FinWhale as a carrier

FinWhale's carrier is the anchored
relation's (`Model/Decided.lean`), and the reverse pass a validator
runs lands in it (`decided_of_wellFormed`), so the properties transfer
to the pass through `passOf` and `decided_of_passOf`. Safety comes from
FinWhale's laws and band laws; liveness from the slow path's support
and the fast path's.
-/

namespace LeanDag

namespace FinWhaleProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **FinWhale as a carrier**: the anchored relation's. -/
abbrev finWhaleRule : DagRule Validator BlockId Payload :=
  (LeanDag.FinWhale.finWhaleAnchored Validator BlockId Payload).toDagRule

/-- **FinWhale's DAGs are quorate**: `ValidHere.quorum`, which asks for
`n − f` distinct authors, read at the carrier. -/
theorem quorate : Quorate (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun D b hb hr => (D.valid b hb).quorum hr

/-- **One block per correct author per round**, from the DAG's
`no_equivocation`. -/
theorem noEquiv : NoEquiv (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun D b c hb hc hbc heq hr => D.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** Lemma 12 under the property's name: the
relation's agreement at FinWhale's laws. -/
theorem agree : Agree (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.agree LeanDag.FinWhale.finWhaleLaws

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate : CommitsCandidate
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  AnchoredRule.commitsCandidate

/-- **A direct commit is a verdict**, at FinWhale's direct predicate as
a view evaluates it, at every schedule. -/
theorem commitsDirect : CommitsDirect
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun {_} V L _ => LeanDag.FinWhale.DirectCommit (V.toRecord) L) :=
  AnchoredRule.commitsDirect

/-! ## Totality and the descent, relationally

The two statements every other arc makes of its anchored rule, from the
same choice at every nonempty rung. Neither mentions a verdict
assignment or the reverse pass: they are facts about the relation, so
they stand whether or not a procedure computing them is present. -/

/-- **The graded rule is total**: a nearest eligible committed anchor
always returns a verdict. -/
theorem total {D : Dag Validator BlockId Payload} {S : Slots Validator} :
    (finWhaleAnchored Validator BlockId Payload).Total (S := S) D :=
  AnchoredRule.total_of_least LeanDag.FinWhale.exists_least

/-- **Every slot below a committed run is decided.** -/
theorem decidedBelowRun {D : Dag Validator BlockId Payload} {S : Slots Validator} :
    (finWhaleAnchored Validator BlockId Payload).DecidedBelowRun (S := S) D :=
  AnchoredRule.decidedBelowRun_of_least LeanDag.FinWhale.exists_least

/-- **FinWhale reads a band**: the relation's band at its band laws. -/
theorem banded : Banded (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  AnchoredRule.banded LeanDag.FinWhale.finWhaleBandLaws

/-- **The indirect rule, with its bound.** The relation's indirect
property at the rung's choice, read at the three-round eligibility:
every rule FinWhale applies at a slot reads the schedule at that slot
alone, which is the relation's `link_congr`. -/
theorem indirect : Indirect
    (finWhaleRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (fun sr i j => sr i + 3 ≤ sr j) :=
  (AnchoredRule.indirect LeanDag.FinWhale.finWhaleLaws.link_congr
    fun hi h => LeanDag.FinWhale.exists_least hi h).congr
    (fun _ _ _ => by simp only [LeanDag.FinWhale.finWhaleAnchored_wave])

/-! ## The pass a view runs

The reverse pass at the carrier's schedule and the DAG's horizon,
well formed at every schedule since a finite validator set stops a
schedule from fitting unboundedly many slots below a round
(`Slots.slot_lt_of_slotRound_le`). -/

/-- A view is finite, so its blocks stop at a round. -/
theorem view_bounded (D : Dag Validator BlockId Payload) (V : D.View) :
    ∀ b ∈ (V.toRecord).ids,
      ((V.toRecord).block b).round ≤
        D.ids.sup (fun c => (D.block c).round) :=
  fun b hb => Finset.le_sup (f := fun c => (D.block c).round) (V.subset_ids hb)

/-- **The pass's horizon**: a slot index above every slot any view of
the DAG can decide. -/
def dagHorizon (D : Dag Validator BlockId Payload) : ℕ :=
  (D.ids.sup (fun b => (D.block b).round) + 1) * Fintype.card Validator

/-- Every slot the pass reaches sits at the schedule's round for it, so
the horizon really is above every slot the pass commits. -/
theorem rle (S : Slots Validator) (D : Dag Validator BlockId Payload) :
    ∀ r, S.slotRound r ≤ D.ids.sup (fun b => (D.block b).round) → r ≤ dagHorizon D :=
  fun _ h => Nat.le_of_lt (LeanDag.Slots.slot_lt_of_slotRound_le (S := S) h)

/-! ## The liveness property

`LeaderCommits` is `Support.leaderCommits` at `fwSupport` below.
FinWhale supplies the slow-path quorum's place inside the correct set
and its certificate condition from coverage, both stated in rounds so
they read at a general schedule. -/

/-- **The slow-path quorum fits inside the correct set.** `n + 1 = 3f + 2p`
with `p ≥ 1` gives `2f + p ≤ n − f`. -/
theorem spQuorum_le_card_correct :
    LeanDag.FinWhale.spQuorum Validator ≤ (Correct : Finset Validator).card := by
  have hq : quorumCard Validator ≤ (Correct : Finset Validator).card := card_correct
  have hc := P.card_add_one
  have hp := P.p_pos
  have hf := P.p_le_f
  have hqc : quorumCard Validator = Fintype.card Validator - F.f := rfl
  have hsp : LeanDag.FinWhale.spQuorum Validator = 2 * F.f + P.p := rfl
  omega

/-- **Every correct validator certifies a correct leader**, on a
synchronised and populated DAG: coverage makes every correct block two
rounds up vote for it through the block one round up. -/
theorem spCommitBy_of_synchronisedOn {D : Dag Validator BlockId Payload} {Rnd r : ℕ}
    (hs : SynchronisedFrom D.block D.ids (Correct : Finset Validator) Rnd)
    (hpop1 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 1))
    (hpop2 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 2))
    (hR : Rnd ≤ r) {L : BlockId} (hL : L ∈ D.ids) (hLr : (D.block L).round = r)
    (hLc : (D.block L).creator ∈ (Correct : Finset Validator)) :
    LeanDag.FinWhale.SPCommitBy D L (Correct : Finset Validator) := by
  refine ⟨(Correct : Finset Validator), Finset.Subset.rfl, spQuorum_le_card_correct, ?_⟩
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop2 v hv
  refine ⟨b, mem_blocksAt.mpr ⟨hb, by rw [hbr, hLr]⟩, hbc, ?_⟩
  refine le_trans spQuorum_le_card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨q, hq, hqc, hqr⟩ := hpop1 w hw
  have hvote : L ∈ (D.block q).refs :=
    hs r hR q hq hqr (by rw [hqc]; exact hw) L hL hLr hLc
  have hpar : q ∈ (D.block b).refs :=
    hs (r + 1) (by omega) b hb hbr (by rw [hbc]; exact hv) q hq hqr (by rw [hqc]; exact hw)
  unfold LeanDag.FinWhale.parentsVoting creatorsOf
  exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hpar, hvote⟩, hqc⟩

/-! ## FinWhale's support shape

The slow path: SP-certificates two rounds above the candidate, each a
block `spQuorum` of whose parents vote. The fast path is latency and
not a liveness shape. -/

/-- The slow-path quorum fits inside any quorum of the fault model:
`n + 1 = 3f + 2p` with `p ≥ 1` gives `2f + p ≤ n − f`. -/
theorem spQuorum_le_quorumCard :
    LeanDag.FinWhale.spQuorum Validator ≤ quorumCard Validator := by
  have hc := P.card_add_one
  have hp := P.p_pos
  have hf := P.p_le_f
  have hqc : quorumCard Validator = Fintype.card Validator - F.f := rfl
  have hsp : LeanDag.FinWhale.spQuorum Validator = 2 * F.f + P.p := rfl
  omega

/-- **FinWhale's support**: wavelength two, certification the slow path's. -/
def fwSupport : Support (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  wave := 2
  Certifies := fun D c l => LeanDag.FinWhale.SPCertificate D c l

/-- **Law 1.** A certifier two rounds above the settling round keeps its
parents, and each parent keeps its parents and its author, so its
voting parents are the same validators. -/
theorem fwSupport_local :
    Support.Local (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) fwSupport := by
  intro D D' G R₀ h c L hc hcr _ _
  change R₀ + 2 ≤ (BlockRecord.block D c).round at hcr
  have hrefs : (BlockRecord.block D' c).refs = (BlockRecord.block D c).refs :=
    h.refs c hc (by change R₀ < (BlockRecord.block D c).round; omega)
  have hpar : ∀ q ∈ (BlockRecord.block D c).refs,
      (BlockRecord.block D' q).refs = (BlockRecord.block D q).refs ∧
      (BlockRecord.block D' q).creator = (BlockRecord.block D q).creator := by
    intro q hq
    have hqD := BlockRecord.complete D c hc q hq
    have hqr := (BlockRecord.valid D c hc).predecessor q hq
    exact ⟨h.refs q hqD (by change R₀ < (BlockRecord.block D q).round; omega),
      h.creator q hqD (by change R₀ ≤ (BlockRecord.block D q).round; omega)⟩
  change LeanDag.FinWhale.SPCertificate D' c L ↔ LeanDag.FinWhale.SPCertificate D c L
  unfold LeanDag.FinWhale.SPCertificate LeanDag.FinWhale.parentsVoting creatorsOf
  rw [hrefs, Finset.filter_congr (fun q hq => by rw [(hpar q hq).1]),
    Finset.image_congr (fun q hq => (hpar q (Finset.mem_of_mem_filter q hq)).2)]

/-- **Law 2.** Coverage toward the candidate over two layers: every
quorum block one round up votes, every quorum block two rounds up
references each voter, and the quorum carries `spQuorum`. -/
theorem fwSupport_ofCoverage :
    Timed.OfCoverage (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) fwSupport (coreReliability Validator) := by
  intro D T hq r L hpop hct hL hLr hLc c hc hcc hcr
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  change LeanDag.FinWhale.spQuorum Validator ≤ (LeanDag.FinWhale.parentsVoting D c L).card
  refine le_trans (le_trans spQuorum_le_quorumCard hcard) (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨q, hq', hqc, hqr⟩ := hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega) w hw
  have hqT : (finWhaleRule.block D q).creator ∈ T := by rw [hqc]; exact hw
  have hvote : L ∈ (BlockRecord.block D q).refs :=
    hct r le_rfl (by change r < r + 2; omega) q hq' hqT hqr L hL hLc hLr
      Relation.ReflTransGen.refl
  have hpar : q ∈ (BlockRecord.block D c).refs :=
    hct (r + 1) (by omega) (by change r + 1 < r + 2; omega) c hc hcc
      (by change (BlockRecord.block D c).round = r + 1 + 1
          rw [show (BlockRecord.block D c).round = r + 2 from hcr])
      q hq' hqT hqr (Relation.ReflTransGen.single (show RefStepFrom (finWhaleRule.block D) q L from hvote))
  unfold LeanDag.FinWhale.parentsVoting creatorsOf
  exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hpar, hvote⟩, hqc⟩

/-- **Law 3.** A quorum's SP-certificates at the slot's candidate, all
held by a view caught up to the certificate round, are a direct commit
on that view, and the pass commits it. -/
theorem fwSupport_commits :
    Support.Commits (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) fwSupport (coreReliability Validator) := by
  intro S D V T k hq hpop hcert hcov hlead
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hLc' : (BlockRecord.block D L).creator = S.leader k := hLc
  have hLr' : (BlockRecord.block D L).round = S.slotRound k := hLr
  have hL : IsLeaderBlock D k L := ⟨hLmem, hLr', hLc'⟩
  have hcom : LeanDag.FinWhale.DirectCommit (V.toRecord) L := by
    refine Or.inr ⟨T, le_trans spQuorum_le_quorumCard hcard, fun v hv => ?_⟩
    · obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 2) (by omega)
        (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega) v hv
      have hbr' : (BlockRecord.block D b).round = S.slotRound k + 2 := hbr
      have hbV : b ∈ V.ids := hcov b hb
        (by change (BlockRecord.block D b).round ≤ S.slotRound k + 2; omega)
      refine ⟨b, ?_, hbc, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hbc hbr⟩
      rw [mem_blocksAt]
      simp only [BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
      exact ⟨hbV, by rw [hbr', hLr']⟩
  refine ⟨L, by omega, LeanDag.FinWhale.Decided.directCommit hL hcom,
    fun S' hround hlead' => ?_⟩
  exact LeanDag.FinWhale.Decided.directCommit (S := S')
    (isLeaderBlock_congr (S₁ := S) (S₂ := S') (congrFun hround k).symm
      (hlead' k (by omega)).symm hL) hcom

/-! ## FinWhale's fast path

`voteSupport`: `n − p` votes one round up, at a fault model of at most
`p` Byzantine validators, which `Params` bounds by `f` but does not
demand; `fwFastReliability` takes it as a hypothesis. -/

/-- **The fast path's fault model**: at most `p` Byzantine validators. -/
def fwFastReliability (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
    (h : F.byzantine.card ≤ P.p) : LeanDag.Reliability Validator where
  correct := (Correct : Finset Validator)
  slack := P.p
  covers := by
    have hc : (Correct : Finset Validator)ᶜ = F.byzantine := by simp [Correct]
    rw [hc]; exact h
  minority := by
    have := P.card_add_one
    have := P.p_pos
    have := P.p_le_f
    omega

/-- **Law 3 of `voteSupport`, for FinWhale's fast path**: `n − p` votes
held by a caught-up view are a fast commit on it, and the pass commits. -/
theorem voteSupport_fast_commits (h : F.byzantine.card ≤ P.p) :
    Support.Commits (R := finWhaleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))
      (voteSupport (finWhaleRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)))
      (fwFastReliability Validator h) := by
  intro S D V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.FinWhale.fastCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - P.p ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hLc' : (BlockRecord.block D L).creator = S.leader k := hLc
  have hLr' : (BlockRecord.block D L).round = S.slotRound k := hLr
  have hL : IsLeaderBlock D k L := ⟨hLmem, hLr', hLc'⟩
  have hcom : LeanDag.FinWhale.DirectCommit (V.toRecord) L := by
    refine Or.inl ?_
    · change LeanDag.FinWhale.fastCard Validator ≤
        (LeanDag.FinWhale.voters (V.toRecord) L).card
      refine le_trans hcard (Finset.card_le_card ?_)
      intro v hv
      obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) v hv
      have hbr' : (BlockRecord.block D b).round = S.slotRound k + 1 := hbr
      have hbV : b ∈ V.ids := hcov b hb
        (by change (BlockRecord.block D b).round ≤ S.slotRound k + 1; omega)
      unfold LeanDag.FinWhale.voters supporters votesFor creatorsOf
      refine Finset.mem_image.mpr ⟨b, ?_, hbc⟩
      rw [Finset.mem_filter, mem_blocksAt]
      simp only [BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
      exact ⟨⟨hbV, by rw [hbr', hLr']⟩, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hbc hbr⟩
  refine ⟨L, by omega, LeanDag.FinWhale.Decided.directCommit hL hcom,
    fun S' hround hlead' => ?_⟩
  exact LeanDag.FinWhale.Decided.directCommit (S := S')
    (isLeaderBlock_congr (S₁ := S) (S₂ := S') (congrFun hround k).symm
      (hlead' k (by omega)).symm hL) hcom

/-! ## The headlines

FinWhale's DAG carries no self-parent clause at the carrier, so it
shows progress, not inclusion. -/

theorem safety : Properties.Safe (finWhaleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Properties.safety banded agree commitsCandidate

theorem progress : Properties.Support.Progresses (fwSupport (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload)) (coreReliability Validator) :=
  Properties.Support.progress fwSupport_commits

end FinWhaleProperties

end LeanDag
