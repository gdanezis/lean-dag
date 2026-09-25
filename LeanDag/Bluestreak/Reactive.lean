import LeanDag.Bluestreak.Liveness
import LeanDag.Reactive.Basic
/-!
# Bluestreak: the pull pacemaker as a reactive schedule

The paper's pacemaker builds a round-`(r + 1)` block once the round-`r`
leader block is *referenceable* — held, with every claim in its causal
history backed by held votes — and a round-`(r + 2)` block once a quorum
of referenceable votes is held, the timeout as fallback. `ReactiveB` is
`ReactiveCore` with those two wait clauses, the referencing discipline
of correct validators, and the format check on certified blocks. What it yields: the
discipline the safety laws assume, the claims the liveness theorems
consume, and every reliable validator deciding a reliable-led slot on
its own view. The step the core does not have is timely
referenceability: a reliable block is referenceable wherever it has
arrived, because its author backed every claim in its cone from its
own holdings, and holdings converge.
-/

namespace LeanDag

namespace Bluestreak

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : Universe Validator BlockId Payload} [ClaimMap BlockId]
variable [S : Slots Validator]
variable {T : Finset Validator} {N R : ℕ} {k : ℕ} {L : BlockId}

/-! ## Referenceability from holdings -/

/-- `L` is backed within the holdings `h`: `n − f` authors of held votes
for it. -/
def BackedIn (U : Universe Validator BlockId Payload) (h : Finset BlockId) (L : BlockId) :
    Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (votesFor U L ((U.block L).round + 1) ∩ h)).card

/-- `X` is referenceable from the holdings `h`: held, with every claim in
its causal history backed within `h`. -/
def Referenceable (U : Universe Validator BlockId Payload) (h : Finset BlockId) (X : BlockId) :
    Prop :=
  X ∈ h ∧ ∀ Y, Reaches U X Y → ∀ L, claim Y = some L → BackedIn U h L

theorem BackedIn.mono {h h' : Finset BlockId} (hh : h ⊆ h') (hb : BackedIn U h L) :
    BackedIn U h' L :=
  le_trans hb (Finset.card_le_card (Finset.image_subset_image (Finset.inter_subset_inter_left hh)))

theorem Referenceable.mono {h h' : Finset BlockId} (hh : h ⊆ h') {X : BlockId}
    (hr : Referenceable U h X) : Referenceable U h' X :=
  ⟨hh hr.1, fun Y hY L hL => (hr.2 Y hY L hL).mono hh⟩

/-- Backed within holdings of the record is certified. -/
theorem certified_of_backedIn {h : Finset BlockId} (hb : BackedIn U h L) : Certified U L :=
  le_trans hb (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-! ## The schedule -/

/-- **Bluestreak's reactive schedule**: the reactive timing, the format
check safety reads, the referencing discipline of correct validators,
and the two wait clauses of the pull pacemaker. -/
structure ReactiveB (U : Universe Validator BlockId Payload) (T : Finset Validator) (N : ℕ)
    extends ReactiveCore U T N where
  /-- A certified block is quorate: what the receivers' format check on
  leader blocks leaves where safety reads it. -/
  certified_quorate : ∀ A ∈ U.ids, Certified U A → Quorate U A
  /-- A correct validator references only what was referenceable from
  its holdings when it built. -/
  refs_referenceable : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    ∀ j ∈ (U.block b).refs, Referenceable U (holds v (built v (n + 1))) j
  /-- A correct validator claims only what its holdings backed when it
  built. -/
  claim_held : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n →
    ∀ L, claim b = some L → BackedIn U (holds v (built v n)) L
  /-- **The leader wait.** At the round above a reliable leader, any
  `T`-authored block either votes, or its builder waited the full
  timeout and votes for the leader block if it is then referenceable. -/
  vote_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 1 →
    L ∈ (U.block c).refs ∨
      (built v (S.slotRound k) + timeout (S.slotRound k) ≤ built v (S.slotRound k + 1) ∧
        (Referenceable U (holds v (built v (S.slotRound k + 1))) L → L ∈ (U.block c).refs))
  /-- **The claim wait.** At two rounds above a reliable leader, any
  `T`-authored block either claims it, or its builder waited the full
  timeout and claims it if it then holds a quorum of referenceable
  votes for it. -/
  claim_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 2 →
    Claims U c L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1) ≤ built v (S.slotRound k + 2) ∧
        ∀ s ⊆ votesFor U L (S.slotRound k + 1),
          (∀ b ∈ s, Referenceable U (holds v (built v (S.slotRound k + 2))) b) →
          quorumCard Validator ≤ (creatorsOf U.block s).card → Claims U c L)

namespace ReactiveB

variable (rb : ReactiveB U T N)

/-! ## The discipline -/

/-- A claim reached from a correct block is backed within its author's
holdings at build time: the block's own claim by `claim_held`, an
inherited one by `refs_referenceable`. -/
theorem backedIn_of_reaches {v : Validator} (hv : v ∈ (Correct : Finset Validator))
    {b X : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = v)
    (hbX : Reaches U b X) (hcl : claim X = some L) :
    BackedIn U (rb.holds v (rb.built v (U.block b).round)) L := by
  rcases hbX.cases_head with rfl | ⟨j, hj, hjX⟩
  · exact rb.claim_held v hv _ b hb hbc rfl L hcl
  · have hr := U.round_of_mem_refs hb hj
    have := rb.refs_referenceable v hv ((U.block j).round) b hb hbc hr.symm j hj
    rw [← hr]
    exact this.2 X hjX L hcl

/-- **The discipline holds of the execution.** -/
theorem disciplined (rb : ReactiveB U T N) : Disciplined U where
  certified_quorate := rb.certified_quorate
  honest_backed := fun B hB hc _ hBX _ hcl =>
    certified_of_backedIn (rb.backedIn_of_reaches hc hB rfl hBX hcl)

/-! ## Timely referenceability -/

/-- A reliable block is referenceable from its author's holdings when
built. -/
theorem referenceable_own (hT : T ⊆ (Correct : Finset Validator)) {u : Validator} (hu : u ∈ T)
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = u) (hN : (U.block b).round ≤ N) :
    Referenceable U (rb.holds u (rb.built u (U.block b).round)) b :=
  ⟨rb.holds_own u hu _ hN b hb hbc rfl,
    fun X hbX L hcl => rb.backedIn_of_reaches (hT hu) hb hbc hbX hcl⟩

/-- **A reliable block is referenceable wherever it has arrived**: its
author's holdings at the build, which back every claim in its cone,
have converged. -/
theorem referenceable_of_converges (hT : T ⊆ (Correct : Finset Validator))
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator = u) (hN : (U.block b).round ≤ N)
    (hgst : rb.gst ≤ rb.built u (U.block b).round) {t : ℕ}
    (ht : rb.built u (U.block b).round + rb.delay ≤ t) :
    Referenceable U (rb.holds v t) b :=
  (rb.referenceable_own hT hu hb hbc hN).mono
    (le_trans (rb.converges v hv u hu _ hgst) (rb.holds_mono v _ _ ht))

/-- A reliable validator's build of a round past `R ≥ gst` lies past `gst`. -/
theorem gst_le_built (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R) {u : Validator}
    (hu : u ∈ T) {n : ℕ} (hR : R ≤ n) (hN : n ≤ N) : rb.gst ≤ rb.built u n :=
  le_trans (le_trans hgst hR) (rb.le_built hu n (rb.toPaceCore.reached hcard n hN u hu))

/-! ## Votes and claims -/

/-- **Every reliable vote block votes.** By the reactive exit, or by the
fallback once the leader block has arrived and is referenceable: it was
built past GST, so it is referenceable at its author's build, and the
collapsed drift plus a timeout of `2Δ + proc` place that build, plus
`delay`, before the waiter's. -/
theorem votes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rb.delay + rb.proc ≤ rb.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + 1 → L ∈ (U.block c).refs := by
  have hD := rb.driftOn_of_catchup hcard hgst
  intro v hv c hc hcc hcr
  rcases rb.vote_or_wait v hv k hN hlead L hL c hc hcc hcr with hvote | ⟨hwait, hheld⟩
  · exact hvote
  · refine hheld (rb.referenceable_of_converges hT hlead hv hL.1 hL.2.2 ?_ ?_ ?_)
    · rw [hL.2.1]; omega
    · rw [hL.2.1]; exact rb.gst_le_built hcard hgst hlead hR (by omega)
    · rw [hL.2.1]
      have hdrift := hD v hv _ hlead (S.slotRound k) hR (by omega)
      have := hto (S.slotRound k) hR
      omega

/-- **Every reliable claim block claims.** By the reactive exit, or by the
fallback once every reliable vote has arrived and is referenceable,
which the same arithmetic one round up gives. -/
theorem claimsAt (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rb.delay + rb.proc ≤ rb.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ClaimsAt U T (S.slotRound k) L := by
  have hD := rb.driftOn_of_catchup hcard hgst
  have hvotes := rb.votes hT hcard hgst hto hR (by omega) hlead hL
  have hpop := rb.toPaceCore.populatedOn hcard (S.slotRound k + 1) (by omega)
  intro v hv c hc hcc hcr
  rcases rb.claim_or_wait v hv k hN hlead L hL c hc hcc hcr with hclaim | ⟨hwait, hfall⟩
  · exact hclaim
  · -- the reliable votes: one block per `u ∈ T`, each a referenceable vote
    classical
    let s : Finset BlockId := (votesFor U L (S.slotRound k + 1)).filter
      fun b => (U.block b).creator ∈ T
    refine hfall s (Finset.filter_subset _ _) (fun b hb => ?_)
      (le_trans hcard (Finset.card_le_card fun u hu => ?_))
    · obtain ⟨hbv, hbT⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbi, hbr, -⟩ := mem_votesFor.mp hbv
      refine rb.referenceable_of_converges hT hbT hv hbi rfl ?_ ?_ ?_
      · rw [hbr]; omega
      · rw [hbr]; exact rb.gst_le_built hcard hgst hbT (by omega) (by omega)
      · rw [hbr]
        have hdrift := hD v hv _ hbT (S.slotRound k + 1) (by omega) (by omega)
        have := hto (S.slotRound k + 1) (by omega)
        omega
    · obtain ⟨b, hb, hbc, hbr⟩ := hpop u hu
      refine mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨?_, hbc ▸ hu⟩, hbc⟩
      exact mem_votesFor.mpr ⟨hb, hbr, hvotes u hu b hb hbc hbr⟩

/-- The claims, from `R` on, for every slot the horizon covers. -/
theorem claimsOn (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rb.delay + rb.proc ≤ rb.timeout n) :
    ClaimsOn U T R := by
  intro k hR hlead L hL v hv c hc hcc hcr
  by_cases hN : S.slotRound k + 2 ≤ N
  · exact rb.claimsAt hT hcard hgst hto hR hN hlead hL v hv c hc hcc hcr
  · have := rb.rounds_le c hc; omega

/-! ## Liveness -/

/-- **Reactive liveness.** A reliable-led slot past GST is committed on
the full view. -/
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rb.delay + rb.proc ≤ rb.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem hcard (rb.claimsOn hT hcard hgst hto) hR hlead
    (rb.toPaceCore.populatedOn hcard _ (by omega))
    (rb.toPaceCore.populatedOn hcard _ hN) _ (View.coversUpto_full U _)

/-- **And locally**: every reliable validator decides it on its own view,
by `latest (r + 2) + delay`, when every reliable claim block has reached
it. -/
theorem decided_local (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rb.delay + rb.proc ≤ rb.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (rb.viewAt v (rb.latest (S.slotRound k + 2) + rb.delay)) k (some L) := by
  obtain ⟨L, hLm, hLc, hLr⟩ :=
    rb.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLm, hLr, hLc⟩
  refine ⟨L, hL, fun v hv => Decided.directCommit hL ?_⟩
  refine directCommitIn_of_claimsAt_held hcard hL (rb.toPaceCore.populatedOn hcard _ hN)
    (rb.claimsAt hT hcard hgst hto hR hN hlead hL) fun c hc hcT hcr => ?_
  exact rb.mem_viewAt (rb.holds_roundBlocks hN
    (fun u hu => rb.gst_le_built hcard hgst hu (by omega) hN) v hv c hc hcT hcr)

/-- **Every slot below a reliable run is decided**: three consecutive
reliable-led slots past GST, within the horizon, decide everything below
them on the full view. -/
theorem decided_below_of_run (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rb.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rb.delay + rb.proc ≤ rb.timeout n)
    (hspan : (bluestreakAnchored Validator BlockId Payload).SpansEligible (S := S) 3)
    {b : ℕ} (hR : R ≤ S.slotRound b) (hN : S.slotRound (b + 2) + 2 ≤ N)
    (hrun : ∀ i, i < 3 → S.leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ v, Decided U (View.full U) i v :=
  Bluestreak.decided_below_of_run hcard hspan (rb.claimsOn hT hcard hgst hto) hR hrun
    (fun n _ hn => rb.toPaceCore.populatedOn hcard n (le_trans hn hN)) _
    (View.coversUpto_full U _)

end ReactiveB

end Bluestreak

end LeanDag
