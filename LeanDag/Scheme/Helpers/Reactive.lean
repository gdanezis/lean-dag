import LeanDag.Scheme.Model.Reactive
import LeanDag.Scheme.Helpers.Support
import LeanDag.Properties.Derived.LeaderCommits
/-!
# The family, run reactively: the wait clauses certify

A reliable set of `q` validators, pacing at `q`, reaches every round
below the horizon (`reached`), as the core's trunk does at `n − f`: the
induction is `PaceCore.reached` with `advancesAt` in place of `advances`.
Production and the collapse of drift follow (`populated`, `driftOn`).

Past GST, with the timeout clearing `2Δ + proc`, a reliable block that
waited holds every reliable block of the round below (`arrives`: the
round below was built by a reliable validator at most `Δ + proc` later,
and arrives `Δ` after). Round by round from the proposal, every reliable
block then reaches the leader block (`reaches`): on the reactive exit by
the clause, on the fallback through the leader's own block of the round
below. A reliable vote-round block therefore votes for it (`votes`), and
a reliable decision-round block certifies it (`certifies`): the vote is the
certificate, or on the fallback the block references every reliable vote.
That is the family support's liveness precondition (`live_of_reactiveLive`),
from which the generic `LeaderCommits` follows.
-/

namespace LeanDag

namespace Scheme

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Nonempty Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} [S : Slots Validator]
variable {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator} {N R q : ℕ}

attribute [local instance] noFaults

namespace SchemeReactive

variable (rs : SchemeReactive q p σ U T N)

omit [P.Mechanised] in
/-- **Every reliable validator reaches every round below the horizon**, when
the reliable set is `q` strong. -/
theorem reached (hq : q ≤ T.card) : ∀ n ≤ N, ∀ v ∈ T, n ≤ rs.top v := by
  intro n
  induction n with
  | zero => intro _ v _; omega
  | succ n ih =>
      intro hn v hv
      refine Nat.succ_le_of_lt (rs.advancesAt v hv n (by omega)
        (max (rs.latest n) rs.gst + rs.delay) (le_trans hq (Finset.card_le_card ?_)))
      intro w hw
      obtain ⟨b, hb, hbc, hbr⟩ := rs.built_of_le_top w hw n (ih (by omega) w hw)
      refine mem_authorsIn.mpr ⟨b, ?_, hbr, hbc⟩
      have hown := rs.holds_own w hw n (by omega) b hb hbc hbr
      have hle : rs.built w n ≤ max (rs.latest n) rs.gst :=
        le_trans (rs.built_le_latest w hw n (by omega)) (le_max_left _ _)
      exact rs.converges v hv w hw _ (le_max_right _ _) (rs.holds_mono w _ _ hle hown)

omit [P.Mechanised] in
include rs in
/-- **Production**: every round below the horizon has a block by every
reliable validator. -/
theorem populated (hq : q ≤ T.card) : ∀ n ≤ N, PopulatedOn U T n :=
  fun n hn v hv => rs.built_of_le_top v hv n (rs.reached hq n hn v hv)

omit [P.Mechanised] in
/-- **Drift collapses** past GST, to `delay + proc`. -/
theorem driftOn (hq : q ≤ T.card) (hgst : rs.gst ≤ R) :
    DriftOn rs.built T R (rs.delay + rs.proc) N := by
  intro v hv w hw n hRn hnN
  have htop := fun u hu => rs.reached hq n hnN u hu
  refine rs.toPaceCore.drift_collapse hnN htop (fun u hu => ?_) w hw v hv
  exact le_trans (le_trans hgst hRn) (rs.toReactiveCore.le_built hu n (htop u hu))

/-- **A reliable block of the round below has arrived** at a reliable
validator that waited the timeout. -/
theorem arrives (hq : q ≤ T.card) (hgst : rs.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) {v u : Validator}
    (hv : v ∈ T) (hu : u ∈ T) {n : ℕ} (hRn : R ≤ n) (hn : n + 1 ≤ N) {b : BlockId}
    (hb : b ∈ U.ids) (hbc : (U.block b).creator = u) (hbr : (U.block b).round = n)
    (hwait : rs.built v n + rs.timeout n ≤ rs.built v (n + 1)) :
    b ∈ rs.holds v (rs.built v (n + 1)) := by
  have hD := rs.driftOn hq hgst
  have hown := rs.holds_own u hu n (by omega) b hb hbc hbr
  have htopu : n ≤ rs.top u := by have := rs.le_top_of_built u hu b hb hbc; omega
  have hgstu : rs.gst ≤ rs.built u n :=
    le_trans (le_trans hgst hRn) (rs.toReactiveCore.le_built hu n htopu)
  have hconv := rs.converges v hv u hu _ hgstu hown
  refine rs.holds_mono v _ _ ?_ hconv
  have hdrift := hD v hv u hu n hRn (by omega)
  have := hto n hRn
  omega

/-- **Every reliable block reaches the leader block**, at each round from the
one above the proposal to the vote round. -/
theorem reaches (hTh : T ⊆ honest) (hq : q ≤ T.card) (hgst : rs.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) {k : ℕ} {L : BlockId}
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + p.voteOffset ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) :
    ∀ m, m < p.voteOffset → ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + m + 1 → Reaches U c L := by
  have step : ∀ m, m < p.voteOffset →
      (∀ b ∈ U.ids, (U.block b).creator = S.leader k → (U.block b).round = S.slotRound k + m →
        Reaches U b L) →
      ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
        (U.block c).round = S.slotRound k + m + 1 → Reaches U c L := by
    intro m hm hbelow v hv c hc hcc hcr
    rcases rs.reach_or_wait v hv k hN hlead L hL m hm c hc hcc hcr with h | ⟨hwait, hincl⟩
    · exact h
    obtain ⟨b, hb, hbc, hbr⟩ :=
      rs.populated hq (S.slotRound k + m) (by omega) (S.leader k) hlead
    have harr := rs.arrives hq hgst hto hv hlead (n := S.slotRound k + m) (by omega)
      (by omega) hb hbc hbr hwait
    exact Reaches.of_mem_refs (hincl b hb hbc hbr harr) (hbelow b hb hbc hbr)
  intro m
  induction m with
  | zero =>
    intro hm
    refine step 0 hm fun b hb hbc hbr => ?_
    rw [U.eq_of_creator_eq hb hL.1 (hTh hlead) hbc hL.2.2 (by rw [hbr, hL.2.1]; rfl)]
  | succ m ih =>
    intro hm
    exact step (m + 1) hm fun b hb hbc hbr =>
      ih (by omega) _ hlead b hb hbc (by omega)

/-- **Every reliable vote-round block votes for the leader block.** -/
theorem votes (hw : 2 ≤ p.waveLength) (hTh : T ⊆ honest) (hq : q ≤ T.card)
    (hgst : rs.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) {k : ℕ}
    {L : BlockId} (hR : R ≤ S.slotRound k) (hN : S.slotRound k + p.voteOffset ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + p.voteOffset → σ.Votes U c L := by
  intro v hv c hc hcc hcr
  have hvo : 1 ≤ p.voteOffset := by
    unfold Params.voteOffset; split <;> omega
  have hre := rs.reaches hTh hq hgst hto hR hN hlead hL (p.voteOffset - 1) (by omega) v hv c
    hc hcc (by omega)
  exact votes_of_reaches_record U.noEquivOn_honest hc hL.1 (hL.2.2 ▸ hTh hlead)
    (by rw [hL.2.1, hcr]; omega) hre

/-- **Every reliable decision-round block certifies the leader block.** -/
theorem certifies (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q)
    (hTh : T ⊆ honest) (hq : q ≤ T.card) (hgst : rs.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) {k : ℕ} {L : BlockId}
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + (p.waveLength - 1) ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + (p.waveLength - 1) → IsCert p σ U c L := by
  intro v hv c hc hcc hcr
  cases hvc : p.voteIsCert with
  | true =>
    have hoff : p.voteOffset = p.waveLength - 1 := by simp [Params.voteOffset, hvc]
    have := rs.votes hw hTh hq hgst hto hR (by omega) hlead hL v hv c hc hcc (by omega)
    unfold IsCert; rw [if_pos hvc]; exact this
  | false =>
    obtain ⟨hw3, hcq⟩ := hcv hvc
    have hoff : p.voteOffset = p.waveLength - 2 := by
      simp only [Params.voteOffset, hvc, Bool.false_eq_true, if_false]; omega
    rcases rs.cert_or_wait hvc v hv k (by omega) hlead L hL c hc hcc (by omega) with
      h | ⟨hwait, hincl⟩
    · exact h
    unfold IsCert; rw [if_neg (by simp [hvc])]
    show p.certThreshold ≤ (creatorsOf U.block (carriedVotes U (σ.Votes U) c L)).card
    refine le_trans hcq (le_trans hq (Finset.card_le_card fun u hu => ?_))
    obtain ⟨b, hb, hbc, hbr⟩ :=
      rs.populated hq (S.slotRound k + p.voteOffset) (by omega) u hu
    have harr := rs.arrives hq hgst hto hv hu (n := S.slotRound k + p.voteOffset) (by omega)
      (by omega) hb hbc hbr hwait
    have hvote := rs.votes hw hTh hq hgst hto hR (by omega) hlead hL u hu b hb hbc hbr
    exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr
      ⟨hincl b hb (hbc ▸ hu) hbr harr hvote, hvote⟩, hbc⟩

end SchemeReactive

omit S in
/-- **The reactive discipline reaches the family support's liveness
precondition**, at any reliability: a reactive execution past GST is a
quorum populating every round of each reliably-led slot's wave and
certifying its candidates. -/
theorem live_of_reactiveLive {Hon : Finset Validator} {rel : Reliability Validator}
    (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false →
      3 ≤ p.waveLength ∧ p.certThreshold ≤ Fintype.card Validator - rel.slack)
    {S : Slots Validator} {U : (schemeRule p σ Hon).Universe} {V : (schemeRule p σ Hon).View U}
    {T : Finset Validator} {lo K : ℕ} (h : reactiveLive p σ Hon rel S V T lo K) :
    (familySupport p σ Hon).live rel S V T lo K := by
  obtain ⟨hT, hTh, N, R₀, rs, hgst, hto, hR, hcov, hN⟩ := h
  refine ⟨hT, N, hcov, fun k hk => hN k hk, fun k hlo hK hlead => ⟨?_, ?_⟩⟩
  · intro n _ h2
    exact rs.populated hT.2 n (le_trans h2 (hN k hK))
  · rintro L ⟨hLmem, hLr, hLc⟩
    exact rs.certifies (S := S) hw hcv hTh hT.2 hgst hto (le_trans hR (S.mono hlo)) (hN k hK)
      hlead ⟨hLmem, hLr, hLc⟩

omit S in
/-- **The family, run reactively, commits its reliable leaders**, at any
reliability whose quorum meets the thresholds. -/
theorem leaderCommits_reactive {Hon : Finset Validator} {rel : Reliability Validator}
    (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false →
      3 ≤ p.waveLength ∧ p.certThreshold ≤ Fintype.card Validator - rel.slack)
    (hcm : p.commitThreshold ≤ Fintype.card Validator - rel.slack) :
    LeaderCommits (schemeRule p σ Hon)
      (fun S {U} V T lo K => reactiveLive p σ Hon rel S (U := U) V T lo K) :=
  fun S _ V T lo K h =>
    Support.leaderCommits (familySupport p σ Hon) (familySupport_commits hcm) S V T lo K
      (live_of_reactiveLive hw hcv h)

end Scheme

end LeanDag
