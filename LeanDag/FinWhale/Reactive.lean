import LeanDag.FinWhale.Decided
import LeanDag.Reactive.Mysticeti
/-!
# FinWhale — liveness on the reactive schedule

FinWhale's pacemaker is reactive. A block of round `r` is created when
any of three conditions holds: C1, the local DAG has the round-`(r−1)`
leader's block together with a quorum of voters for the round-`(r−2)`
leader (or an SP-skip pattern for it); C2, the `2∆` timeout has expired;
or C3, the local DAG has `n − f` round-`r` blocks. The timeout is the
fallback, not the rule.

`Liveness.lean` derives coverage from `ViewPace`, whose `waits` field is
a waiting **floor** — a validator never builds before the timeout
expires. That is the C2-only discipline. It is a consistent structure and
the results over it are not vacuous, but it is not the schedule FinWhale
describes, and coverage is exactly what a reactive builder does not
have: it omits whatever had not arrived when its exit fired.

This file runs the same liveness off `ReactivePace` instead, where the
floor is replaced by a ceiling (`deadline`) and two wait clauses:

* `vote_or_wait` — a round-`(r+1)` block either references the round-`r`
  leader's block, or its builder waited the full timeout and would have
  referenced it had it held it. This is what FinWhale's Lemma 18 proves
  by case analysis on C1, C2 and C3, taken here as the discipline's
  clause rather than re-derived from the pseudocode.
* `cert_or_wait` — a round-`(r+2)` block either already carries a quorum
  of votes among its parents, or its builder waited the full timeout and
  references every reliable vote it holds. This is FinWhale's Lemma 19,
  and it is also where the paper's parent-selection rule enters: a
  C1-triggered block references the blocks satisfying L1 and L2 by
  construction.

Nothing else changes. **Mysticeti's certificate is FinWhale's
SP-certificate**, since the slow-path quorum `2f + p` is no larger than
the validity quorum `n − f`, so the reactive certificate stage the core
already proves (`ReactiveM.certifies`) supplies the slow-path commit
directly, and the votes it rests on supply the fast one.

The route ends where the timed one does, at `CommitsCorrectLeaders`:
every correct-led slot below the horizon carries a direct commit. Lemma
23 and the theorems above it consume that interface and never learn which
schedule produced it.
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
/-- **Mysticeti's certificate is FinWhale's.** Both count the parents
that vote, and FinWhale asks for `2f + p` where the validity quorum is
`n − f`, which is no smaller. -/
theorem spCertificate_of_certifies (hblk : D.block = U.block) {c : BlockId}
    (h : Certifies U c L) : SPCertificate D c L := by
  change spQuorum Validator ≤ (parentsVoting D c L).card
  have heq : parentsVoting D c L = creatorsOf U.block (votesIn U c L) := by
    simp only [parentsVoting, votesIn, carriedVotes, hblk]
  rw [heq]
  exact le_trans (spQuorum_le_quorumCard (Validator := Validator)) h

/-- **Lemma 20 on the reactive route.** The reliable validators' own
round-`(r+2)` blocks are certificates for a reliable leader's block, and
there are `n − f ≥ 2f + p` of them. -/
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

/-- **Theorem 21 on the reactive route.** Where at most `p` validators
are Byzantine, the reliable validators' votes alone are a fast commit —
and the reactive exit is what makes them votes. -/
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

Theorem 21 says the fast commit exists. Definition 1 says more: that it
happens "within two message delays" when the network is momentarily
synchronous. The reactive schedule is where that can be said, because its
exit is not bounded below by the timeout, and the core proves the bound
for any protocol on it. -/

/-- **The fast commit, and when its votes are built.** Under
`δ`-propagation past GST and at most `p` actual faults, the correct
validators' round-`(r+1)` blocks all vote for a correct leader's block —
which is a fast commit — and each is built within `Δ + δ + 2·proc` of its
author entering round `r`: the collapsed spread, one delivery, and two
processing steps. The timeout does not appear. -/
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
