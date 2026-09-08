import LeanDag.Mysticeti.ViewPace
/-!
# The reactive schedule

Where the timed schedule of §6.9 waits a full timeout every round, the
reactive one builds as soon as its exit condition fires — a leader vote
or, failing that, the full timeout — trading reference coverage for
latency: a reactive builder omits whatever had not arrived, so
`SynchronisedOn` fails in general and only what the commit rule counts
survives. `prompt_vote` bounds the fast exit, giving the latency and
no-timeout theorems below it. `ReactivePace` extends the same `PaceCore`
trunk as the full-timeout discipline, so production is inherited rather
than assumed.
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {D N R : ℕ} {k : ℕ} {L : BlockId}

/-- The reactive schedule and network layer, shared by both protocols:
`PaceCore` with `deadline`, `built_lt`, `vote_or_wait` and `prompt_vote`
in place of `ViewPace`'s full-timeout floor. -/
structure ReactivePace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends PaceCore U T N where
  /-- Time advances with rounds — the only lower bound a reactive
  schedule keeps, over the rounds `v` reached. -/
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- **The reactive ceiling.** A validator never waits past the
  timeout; it may build any time before it. -/
  deadline : ∀ v ∈ T, ∀ n < top v, built v (n + 1) ≤ built v n + timeout n
  /-- **The leader wait.** At the round above a reliable leader, any
  `T`-authored block either votes (the reactive exit), or its builder
  waited the full timeout and votes for any leader block it holds (the
  fallback). -/
  vote_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 1 →
    L ∈ (U.block c).refs ∨
      (built v (S.slotRound k) + timeout (S.slotRound k)
          ≤ built v (S.slotRound k + 1) ∧
        (L ∈ holds v (built v (S.slotRound k + 1)) → L ∈ (U.block c).refs))
  /-- **The reactive exit is prompt.** Once a validator past its round
  entry holds the leader and every reliable round-`r` block, it builds
  within `proc`. Consumed only by the fast-path results. -/
  prompt_vote : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L → ∀ t, built v (S.slotRound k) ≤ t →
    L ∈ holds v t →
    (∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = S.slotRound k →
      b ∈ holds v t) →
    built v (S.slotRound k + 1) ≤ t + proc

namespace ReactivePace

variable (rc : ReactivePace U T N)

omit [DecidableEq BlockId] in
/-- Rounds advance real time, over the rounds a validator reached. -/
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ rc.top v, n ≤ rc.built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
      intro hn
      have := rc.built_lt v hv n (by omega)
      have := ih (by omega)
      omega

omit [DecidableEq BlockId] in
/-- A reliable leader reached its slot's round: its block is in the
universe, and `le_top_of_built` reads the reach off it. No production
argument and no quorum is needed for this direction. -/
theorem slotRound_le_top (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    S.slotRound k ≤ rc.top (S.leader k) := by
  have h1 := rc.le_top_of_built (S.leader k) hlead L hL.1 hL.2.2
  have h2 := hL.2.1
  omega

omit [DecidableEq BlockId] in
/-- **Drift is derived here too**, from the trunk's catch-up rule — the
same collapse the timed discipline uses, with `le_built` supplied by
`built_lt` rather than by the waiting floor. -/
theorem driftOn_of_catchup
    (hcard : quorumCard Validator ≤ T.card) (hgst : rc.gst ≤ R) :
    DriftOn rc.built T R (rc.delay + rc.proc) N :=
  rc.toPaceCore.driftOn_of_catchup hcard hgst (fun u hu => rc.le_built hu)

/-- **Every reliable vote block votes.** Past GST, with the timeout
clearing `2Δ + proc`, every `T`-authored block at the round above a
reliable leader references it — by the reactive exit directly, or by
the fallback once convergence and the collapsed drift place the
leader's arrival before the waiter's build. -/
theorem votes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    VotesAt U T (S.slotRound k) L := by
  have hD := rc.driftOn_of_catchup hcard hgst
  intro v hv c hc hcc hcr
  rcases rc.vote_or_wait v hv k hN hlead L hL c hc hcc hcr with hvote | ⟨hwait, hheld⟩
  · exact hvote
  · refine hheld ?_
    -- the leader's own copy, carried across by convergence
    have hown := rc.holds_own _ hlead (S.slotRound k) (by omega) L hL.1 hL.2.2 hL.2.1
    have hgstL : rc.gst ≤ rc.built (S.leader k) (S.slotRound k) :=
      le_trans (le_trans hgst hR)
        (rc.le_built hlead _ (rc.slotRound_le_top hlead hL))
    have hconv := rc.converges v hv _ hlead _ hgstL hown
    refine rc.holds_mono v _ _ ?_ hconv
    have hdrift := hD v hv _ hlead (S.slotRound k) hR (by omega)
    have := hto (S.slotRound k) hR
    omega

end ReactivePace

/-! ## The fast path

The theorems above use only the fallback. These two use only the exit:
when delivery outpaces the timeout, latency tracks delivery, and the
timeout never fires. `δ` is the *actual* per-block propagation bound of
the execution — a premise about this run, not an assumption about the
network in general — and the conclusions degrade continuously as it
approaches the timeout. -/

namespace ReactivePace

variable (rc : ReactivePace U T N)

omit [DecidableEq BlockId] in
/-- **Latency tracks delivery.** If every reliable round-`r` block —
the leader's among them — reaches every reliable validator within `δ`
of its build, then the round above is built within `D + δ + proc` of
round entry: drift to the last builder, `δ` to arrive, `proc` to build.
The timeout does not appear. -/
theorem built_succ_le_of_fast {δ : ℕ}
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      ≤ rc.built v (S.slotRound k) + D + δ + rc.proc := by
  intro v hv
  refine rc.prompt_vote v hv k hN hlead L hL
    (rc.built v (S.slotRound k) + D + δ) (by omega) ?_ ?_
  · have := hδ v hv L hL.1 (hL.2.2 ▸ hlead) hL.2.1
    rw [hL.2.2] at this
    refine rc.holds_mono v _ _ ?_ this
    have := hD _ hlead v hv
    omega
  · intro b hb hbT hbr
    refine rc.holds_mono v _ _ ?_ (hδ v hv b hb hbT hbr)
    have := hD _ hbT v hv
    omega

omit [DecidableEq BlockId] in
/-- **The timeout never fires.** When delivery, drift and processing
together undercut the timeout, every reliable validator builds strictly
before its deadline — the fallback branch of `vote_or_wait` is never
taken, and consensus proceeds at network speed. -/
theorem no_timeout_of_fast {δ : ℕ}
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator))
    (hfast : D + δ + rc.proc < rc.timeout (S.slotRound k)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      < rc.built v (S.slotRound k) + rc.timeout (S.slotRound k) := by
  intro v hv
  have := rc.built_succ_le_of_fast hδ hD hN hlead hL hT v hv
  omega

/-! ### The spread, discharged

Past GST the catch-up rule collapses the spread `D` to `delay + proc`,
so latency below is stated in the deployment's own constants. -/

omit [DecidableEq BlockId] in
/-- **Latency, in the deployment's own constants.** Past GST, with a quorum
reliable, every reliable validator builds the round above within
`Δ + δ + 2 * proc` of entering it: `Δ + proc` of collapsed spread to the last
builder, `δ` for the block to arrive, `proc` to build on it. No free spread
parameter, and the timeout does not appear. -/
theorem built_succ_le_of_fast_gst {δ : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : rc.gst ≤ R)
    (hR : R ≤ S.slotRound k)
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      ≤ rc.built v (S.slotRound k) + rc.delay + δ + 2 * rc.proc := by
  have hdrift := rc.driftOn_of_catchup hcard hgst
  have hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + (rc.delay + rc.proc) :=
    fun u hu v hv => hdrift v hv u hu (S.slotRound k) hR (by omega)
  intro v hv
  have := rc.built_succ_le_of_fast hδ hD hN hlead hL hT v hv
  omega

omit [DecidableEq BlockId] in
/-- **When the timeout never fires**, in the same constants. At the minimal
timeout `2Δ + proc` the hypothesis reads `δ + proc < Δ`: the fallback is dead
exactly when actual delivery, plus one processing step, beats the bound the
timeout was set against. -/
theorem no_timeout_of_fast_gst {δ : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : rc.gst ≤ R)
    (hR : R ≤ S.slotRound k)
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator))
    (hfast : rc.delay + δ + 2 * rc.proc < rc.timeout (S.slotRound k)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      < rc.built v (S.slotRound k) + rc.timeout (S.slotRound k) := by
  intro v hv
  have := rc.built_succ_le_of_fast_gst hcard hgst hR hδ hN hlead hL hT v hv
  omega

end ReactivePace

end LeanDag
