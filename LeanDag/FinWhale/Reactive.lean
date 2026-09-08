import LeanDag.FinWhale.Decided
import LeanDag.Reactive.Mysticeti
/-!
# FinWhale — liveness on the reactive schedule

FinWhale's pacemaker is reactive: a block is created on C1 (the leader's
block plus votes or an SP-skip pattern), C2 (the timeout), or C3 (`n − f`
blocks of the round), the timeout being a fallback rather than the rule.
`Liveness.lean`'s `ViewPace` is C2-only and does not match this, since
coverage needs what a reactive builder may not have. This file runs the
same liveness off `ReactivePace`'s two wait clauses instead —
`vote_or_wait` (Lemma 18) and `cert_or_wait` (Lemma 19) — and reads
Mysticeti's certificate as FinWhale's SP-certificate, since the
slow-path quorum `2f + p` is no larger than the validity quorum `n − f`.
The route ends at `CommitsCorrectLeaders`, as the timed one does.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Dag Validator BlockId Payload} {FS : Slots Validator}
variable [S : Slots Validator]
variable {T : Finset Validator} {N R k : ℕ} {L : BlockId}

omit S in
/-- **Mysticeti's certificate is FinWhale's**: both count voting parents,
and FinWhale's `2f + p` is no larger than the validity quorum. -/
theorem spCertificate_of_certifies (hblk : D.block = U.block) {c : BlockId}
    (h : Certifies U c L) : SPCertificate D c L := by
  change spQuorum Validator ≤ (parentsVoting D c L).card
  have heq : parentsVoting D c L = creatorsOf U.block (votesIn U c L) := by
    simp only [parentsVoting, votesIn, carriedVotes, hblk]
  rw [heq]
  exact le_trans (spQuorum_le_quorumCard (Validator := Validator)) h

/-- **Lemma 20 on the reactive route**: the reliable validators'
round-`(r+2)` blocks are certificates for a reliable leader's block,
`n − f ≥ 2f + p` of them. -/
theorem spCommit_of_reactive (rm : ReactiveM U T N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    SPCommitBy D L T := by
  have hcert := rm.certifies hT hcard hgst hto hR hN hlead hL
  have hpop := rm.toPaceCore.populatedOn hcard (S.slotRound k + 2) (by omega)
  have hLround : (D.block L).round = S.slotRound k := by rw [hblk]; exact hL.2.1
  refine ⟨T, Finset.Subset.refl T,
    le_trans (spQuorum_le_quorumCard (Validator := Validator)) hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
  refine ⟨b, ?_, by rw [hblk]; exact hbc,
    spCertificate_of_certifies hblk (hcert v hv b hb hbc hbr)⟩
  simp only [blocksAt, Finset.mem_filter, hids, hblk, hL.2.1]
  exact ⟨hb, hbr⟩

/-- **Theorem 21 on the reactive route**: where at most `p` validators
are Byzantine, the reliable validators' votes alone are a fast
commit. -/
theorem fastCommit_of_reactive (rc : ReactivePace U T N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hTeq : T = (Correct : Finset Validator)) (hfew : F.byzantine.card ≤ P.p)
    (hgst : rc.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    FastCommit D L := by
  subst hTeq
  have hvotes := rc.votes (fun _ h => h) card_correct hgst hto hR hN hlead hL
  have hpop := rc.toPaceCore.populatedOn card_correct (S.slotRound k + 1) (by omega)
  have hLround : (D.block L).round = S.slotRound k := by rw [hblk]; exact hL.2.1
  have hsub : (Correct : Finset Validator) ⊆ voters D L := by
    intro v hv
    obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
    refine mem_creatorsOf.2 ⟨b, ?_, by rw [hblk]; exact hbc⟩
    simp only [votesFor, Finset.mem_filter, blocksAt, hids, hblk, hL.2.1]
    exact ⟨⟨hb, hbr⟩, hvotes v hv b hb hbc hbr⟩
  have hcard : fastCard Validator ≤ (Correct : Finset Validator).card := by
    have := card_correct_add_byzantine (Validator := Validator)
    simp only [fastCard]; omega
  exact le_trans hcard (Finset.card_le_card hsub)

/-! ## Definition 1's latency

Theorem 21 says the fast commit exists; Definition 1 says it happens
within two message delays under momentary synchrony, which the reactive
schedule can state since its exit is not bounded below by the
timeout. -/

/-- **The fast commit, and when its votes are built**: under
`δ`-propagation past GST and at most `p` actual faults, every correct
round-`(r+1)` block votes and is built within `Δ + δ + 2·proc` of its
author entering round `r`, with no timeout involved. -/
theorem fastCommit_latency (rc : ReactivePace U T N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hTeq : T = (Correct : Finset Validator)) (hfew : F.byzantine.card ≤ P.p)
    (hgst : rc.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L)
    {δ : ℕ} (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ)) :
    FastCommit D L ∧
      ∀ v ∈ T, rc.built v (S.slotRound k + 1)
        ≤ rc.built v (S.slotRound k) + rc.delay + δ + 2 * rc.proc := by
  refine ⟨fastCommit_of_reactive rc hids hblk hTeq hfew hgst hto hR hN hlead hL, ?_⟩
  subst hTeq
  exact rc.built_succ_le_of_fast_gst card_correct hgst hR hδ hN hlead hL (fun _ h => h)

omit P [DecidableEq BlockId] in
/-- **And the timeout never fires**, where actual delivery beats it. This
is Definition 1's "momentarily synchronous" clause: the fallback branch
of the vote rule is dead, and the round advances at network speed. -/
theorem no_timeout_of_fast (rc : ReactivePace U T N)
    (hTeq : T = (Correct : Finset Validator))
    (hgst : rc.gst ≤ R) (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L)
    {δ : ℕ} (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hfast : rc.delay + δ + 2 * rc.proc < rc.timeout (S.slotRound k)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      < rc.built v (S.slotRound k) + rc.timeout (S.slotRound k) := by
  subst hTeq
  exact rc.no_timeout_of_fast_gst card_correct hgst hR hδ hN hlead hL (fun _ h => h) hfast

/-- **The reactive route supplies the liveness interface.** Every
correct-led slot below the horizon carries a direct commit, with the
schedule's two wait clauses in place of coverage.

`hround` and `hleader` say the ambient slot schedule is the DAG's: one
slot per round, and the same leader. -/
theorem commits_of_reactive (rm : ReactiveM U T N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hround : ∀ k, S.slotRound k = k) (hfr : ∀ k, FS.slotRound k = k)
    (hleader : ∀ k, FS.leader k = S.leader k)
    (hTeq : T = (Correct : Finset Validator))
    (hgst : rm.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) :
    CommitsCorrectLeaders FS D R N := by
  subst hTeq
  intro s hR hN hsc
  rw [hfr] at hR hN
  obtain ⟨L, hL, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn card_correct s (by omega) (FS.leader s) hsc
  have hsr : S.slotRound s = s := hround s
  have hLb : IsLeaderBlock U s L := ⟨hL, by rw [hLr, hsr], by rw [hLc, hleader]⟩
  obtain ⟨certs, hcertsub, hcard, hcertb⟩ :=
    spCommit_of_reactive rm hids hblk (fun _ h => h) card_correct hgst hto
      (by rw [hsr]; exact hR) (by rw [hsr]; omega) (by rw [← hleader]; exact hsc) hLb
  refine ⟨L, ?_, certs, hcertsub, hcard, hcertb⟩
  simp only [slotBlocks, leaderBlocksAt, blocksAt, Finset.mem_filter, hids, hblk, hfr]
  exact ⟨⟨hL, hLr⟩, hLc⟩

end FinWhale

end LeanDag
