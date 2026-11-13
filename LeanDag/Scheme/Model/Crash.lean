import LeanDag.Scheme.Model.Reactive
import LeanDag.Scheme.Model.AsyncPace
/-!
# The family, run with crashes and restarts

A validator may stop and start again, and so may all of them. `up v t`
says that `v` is running at time `t`. A crash run (`CrashRun`) is a
responsive run (`SchemeReactive`) in which:

* **what survives a crash holds throughout.** A validator writes every
  block it accepts or builds to disk before acting on it, so what it holds
  only grows (`holds_mono`) and it holds its own block from the time it
  builds it (`holds_own`). It builds only while up (`up_built`). On
  restart it builds every round it missed, so its blocks are rounds `0`
  to `top v` with none skipped (`built_of_le_top`). Its timers are set
  again at the restart, so a block it builds after waiting waited at
  least the timeout since the round below, and the wait clauses hold of
  every block (`reach_or_wait`, `cert_or_wait`);
* **what needs the validator running holds only while it runs.** The
  network delivers to a validator up throughout the delay what a running
  validator holds, which covers what was sent while it was down, since on
  restart it asks again for what it lacks (`converges`); a validator up
  throughout the processing time enters a round it sees (`catchup`); and a
  validator up from one round to the next does not wait past the timeout
  (`deadline`);
* **the reliable validators stay up from `tr` on** (`up_from`). Before
  `tr` any of them may crash and restart any number of times; every
  validator may be down at once.

`CrashRun.toReactive` reads a crash run as a responsive run past
`max gst tr`, and `crashLive` is the liveness precondition of a crash run,
as `reactiveLive` is of a responsive one.

Asynchronously (`AsyncCrashRun`) there is no clock to lose: what a running
validator holds reaches every reliable validator that runs from some time
on, and `AsyncCrashRun.toAsyncPace` reads such a run as an asynchronous
one. A timed crash run forgets its clock into one (`CrashRun.toAsync`).

Definitions only; the claims are `Scheme/Crash/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Nonempty Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

attribute [local instance] noFaults

/-- **`v` is up from `a` to `b`.** -/
def UpOn (up : Validator → ℕ → Prop) (v : Validator) (a b : ℕ) : Prop :=
  ∀ s, a ≤ s → s ≤ b → up v s

/-- **The family, run with crashes and restarts**, at quorum `q`. -/
structure CrashRun [S : Slots Validator] (q : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ) where
  /-- The highest round `v` reached. -/
  top : Validator → ℕ
  /-- When `v` built its round-`n` block. -/
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  proc : ℕ
  latest : ℕ → ℕ
  /-- What `v` holds at time `t`, on its disk. -/
  holds : Validator → ℕ → Finset BlockId
  /-- Whether `v` is running at time `t`. -/
  up : Validator → ℕ → Prop
  /-- The time from which the reliable validators stay up. -/
  tr : ℕ
  /-- **The reliable validators stay up from `tr` on.** -/
  up_from : ∀ v ∈ T, ∀ t, tr ≤ t → up v t
  /-- **A validator builds only while up.** -/
  up_built : ∀ v ∈ T, ∀ n ≤ top v, up v (built v n)
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  /-- **Every round `v` reached, it built in**: on restart it builds every
  round it missed. -/
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  le_top_of_built : ∀ v ∈ T, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round ≤ top v
  timeout_pos : ∀ n, 1 ≤ timeout n
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  holds_sub : ∀ v, ∀ t, holds v t ⊆ U.ids
  holds_closed : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t, ∀ j ∈ (U.block b).refs, j ∈ holds v t
  refs_held : ∀ v ∈ T, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ holds v (built v (n + 1))
  /-- **Persistence**: a validator holds its own block from the time it
  built it, across crashes. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  /-- **Persistence**: what a validator holds survives a crash. -/
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **Delivery to a running validator.** Past GST, what a running
  validator holds reaches a validator up throughout the delay. -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → up w t → UpOn up v t (t + delay) →
    holds w t ⊆ holds v (t + delay)
  /-- A validator holding every author of a round gets past it. -/
  advances : ∀ v ∈ T, ∀ n < N, ∀ t,
    Fintype.card Validator ≤ (authorsIn U (holds v t) n).card → n < top v
  /-- **Catch-up while running.** Past GST, a validator up throughout the
  processing time enters a round it sees. -/
  catchup : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator ∈ T → (U.block b).round = n →
    ∀ t, gst ≤ t → UpOn up v t (t + proc) → b ∈ holds v t → n ≤ top v ∧ built v n ≤ t + proc
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- **The ceiling while running.** Past GST, a validator up from one
  round to the next does not wait past the timeout. -/
  deadline : ∀ v ∈ T, ∀ n < top v, gst ≤ built v n → UpOn up v (built v n) (built v (n + 1)) →
    built v (n + 1) ≤ built v n + timeout n
  advancesAt : ∀ v ∈ T, ∀ n < N, ∀ t, q ≤ (authorsIn U (holds v t) n).card → n < top v
  /-- **Reach or wait**, of every block, timers set again on restart. -/
  reach_or_wait : ∀ v ∈ T, ∀ k : ℕ, gst ≤ S.slotRound k →
    S.slotRound k + p.voteOffset ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L → ∀ m, m < p.voteOffset →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + m + 1 →
    Reaches U c L ∨
      (built v (S.slotRound k + m) + timeout (S.slotRound k + m)
          ≤ built v (S.slotRound k + m + 1) ∧
        ∀ b ∈ U.ids, (U.block b).creator = S.leader k → (U.block b).round = S.slotRound k + m →
          b ∈ holds v (built v (S.slotRound k + m + 1)) → b ∈ (U.block c).refs)
  /-- **Certify or wait**, of every block, timers set again on restart. -/
  cert_or_wait : p.voteIsCert = false → ∀ v ∈ T, ∀ k : ℕ, gst ≤ S.slotRound k →
    S.slotRound k + p.voteOffset + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + p.voteOffset + 1 →
    IsCert p σ U c L ∨
      (built v (S.slotRound k + p.voteOffset) + timeout (S.slotRound k + p.voteOffset)
          ≤ built v (S.slotRound k + p.voteOffset + 1) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + p.voteOffset →
          b ∈ holds v (built v (S.slotRound k + p.voteOffset + 1)) → σ.Votes U b L →
          b ∈ (U.block c).refs)

/-- **A crash run, read past `max gst tr`, is a responsive run**: from then
on every reliable validator is up, so delivery, catch-up and the ceiling
hold as they do without crashes. -/
def CrashRun.toReactive [S : Slots Validator] {q : ℕ} {p : Params}
    {σ : VoteSel Validator BlockId Payload P honest}
    {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator} {N : ℕ}
    (cr : CrashRun q p σ U T N) : SchemeReactive q p σ U T N where
  top := cr.top
  built := cr.built
  timeout := cr.timeout
  gst := max cr.gst cr.tr
  delay := cr.delay
  proc := cr.proc
  latest := cr.latest
  holds := cr.holds
  rounds_le := cr.rounds_le
  built_of_le_top := cr.built_of_le_top
  le_top_of_built := cr.le_top_of_built
  timeout_pos := cr.timeout_pos
  built_le_latest := cr.built_le_latest
  holds_sub := cr.holds_sub
  holds_closed := cr.holds_closed
  refs_held := cr.refs_held
  holds_own := cr.holds_own
  holds_mono := cr.holds_mono
  converges := fun v hv w hw t ht =>
    cr.converges v hv w hw t (le_trans (le_max_left _ _) ht)
      (cr.up_from w hw t (le_trans (le_max_right _ _) ht))
      (fun s hs _ => cr.up_from v hv s (le_trans (le_max_right _ _) (le_trans ht hs)))
  advances := fun v hv n hn t h => cr.advances v hv n hn t h
  catchup := fun v hv n hn b hb hbT hbr t ht hheld =>
    cr.catchup v hv n hn b hb hbT hbr t (le_trans (le_max_left _ _) ht)
      (fun s hs _ => cr.up_from v hv s (le_trans (le_max_right _ _) (le_trans ht hs))) hheld
  built_lt := cr.built_lt
  deadline := fun v hv n hn ht =>
    cr.deadline v hv n hn (le_trans (le_max_left _ _) ht)
      (fun s hs _ => cr.up_from v hv s (le_trans (le_max_right _ _) (le_trans ht hs)))
  advancesAt := cr.advancesAt
  reach_or_wait := fun v hv k hk => cr.reach_or_wait v hv k (le_trans (le_max_left _ _) hk)
  cert_or_wait := fun hvc v hv k hk => cr.cert_or_wait hvc v hv k (le_trans (le_max_left _ _) hk)

/-- **The crash liveness precondition**, at reliability `rel`, over a slot
window: a quorum `T` of `rel` of honest validators running a crash run at
`n − rel.slack`, the window past `max gst tr`, the timeout clearing
`2Δ + proc`, the view caught up to the horizon. -/
def crashLive (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (S : Slots Validator)
    {U : (schemeRule p σ).Universe} (V : (schemeRule p σ).View U) (T : Finset Validator)
    (lo K : ℕ) : Prop :=
  rel.IsQuorum T ∧ T ⊆ honest ∧
    ∃ (N R₀ : ℕ) (cr : CrashRun (S := S) (Fintype.card Validator - rel.slack) p σ U T N),
      max cr.gst cr.tr ≤ R₀ ∧ (∀ n, R₀ ≤ n → 2 * cr.delay + cr.proc ≤ cr.timeout n) ∧
      R₀ ≤ S.slotRound lo ∧ Properties.CoversUpto (schemeRule p σ) V N ∧
      ∀ k, k < K → S.slotRound k + (p.waveLength - 1) ≤ N

/-- **The family, run asynchronously with crashes and restarts**, at
quorum `q`: an asynchronous run whose delivery reaches only validators
that run from some time on. -/
structure AsyncCrashRun (q : ℕ) (U : BlockRecord Validator BlockId Payload P honest)
    (T : Finset Validator) (N : ℕ) where
  /-- The highest round `v` reached. -/
  top : Validator → ℕ
  /-- **Every round `v` reached, it built in**: on restart it builds every
  round it missed. -/
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  /-- What `v` holds at time `t`, on its disk. -/
  holds : Validator → ℕ → Finset BlockId
  holds_sub : ∀ v, ∀ t, holds v t ⊆ U.ids
  holds_closed : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t, ∀ j ∈ (U.block b).refs, j ∈ holds v t
  /-- **Persistence**: what a validator holds survives a crash. -/
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  holds_own : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v → ∃ t, b ∈ holds v t
  /-- Whether `v` is running at time `t`. -/
  up : Validator → ℕ → Prop
  /-- The time from which the reliable validators stay up. -/
  tr : ℕ
  /-- **The reliable validators stay up from `tr` on.** -/
  up_from : ∀ v ∈ T, ∀ t, tr ≤ t → up v t
  /-- **Eventual delivery to a validator that runs from some time on**:
  what a running reliable validator holds, such a validator holds later. -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, up w t → (∃ s, ∀ s', s ≤ s' → up v s') →
    ∃ d, holds w t ⊆ holds v (t + d)
  advancesAt : ∀ v ∈ T, ∀ n < N, ∀ t, q ≤ (authorsIn U (holds v t) n).card → n < top v

/-- **An asynchronous crash run is an asynchronous run**: a block a
reliable validator holds at `t` it still holds once up, at `max t tr`, and
from then on every reliable validator runs. -/
def AsyncCrashRun.toAsyncPace {q N : ℕ} {U : BlockRecord Validator BlockId Payload P honest}
    {T : Finset Validator} (ac : AsyncCrashRun q U T N) : AsyncPace q U T N where
  top := ac.top
  built_of_le_top := ac.built_of_le_top
  holds := ac.holds
  holds_sub := ac.holds_sub
  holds_closed := ac.holds_closed
  holds_mono := ac.holds_mono
  holds_own := ac.holds_own
  converges := fun v hv w hw t => by
    obtain ⟨d, hd⟩ := ac.converges v hv w hw (max t ac.tr)
      (ac.up_from w hw _ (le_max_right _ _)) ⟨ac.tr, fun s' hs' => ac.up_from v hv s' hs'⟩
    refine ⟨max t ac.tr + d - t, fun b hb => ?_⟩
    have := hd (ac.holds_mono w t _ (le_max_left _ _) hb)
    rwa [show t + (max t ac.tr + d - t) = max t ac.tr + d by omega]
  advancesAt := ac.advancesAt

/-- **A crash run forgets its clock**: past GST, delivery to a validator up
throughout the delay is delivery to one that runs from some time on. -/
def CrashRun.toAsync [S : Slots Validator] {q : ℕ} {p : Params}
    {σ : VoteSel Validator BlockId Payload P honest}
    {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator} {N : ℕ}
    (cr : CrashRun q p σ U T N) : AsyncCrashRun q U T N where
  top := cr.top
  built_of_le_top := cr.built_of_le_top
  holds := cr.holds
  holds_sub := cr.holds_sub
  holds_closed := cr.holds_closed
  holds_mono := cr.holds_mono
  holds_own := fun v hv b hb hbc =>
    ⟨_, cr.holds_own v hv _ (cr.rounds_le b hb) b hb hbc rfl⟩
  up := cr.up
  tr := cr.tr
  up_from := cr.up_from
  converges := fun v hv w hw t hup ⟨s, hs⟩ => by
    -- deliver from a time past GST at which both run, carrying `w`'s holdings there
    have hw' : cr.up w (max t (max cr.gst (max cr.tr s))) := cr.up_from w hw _ (by omega)
    have h := cr.converges v hv w hw (max t (max cr.gst (max cr.tr s))) (by omega) hw'
      (fun s' hs' _ => hs s' (by omega))
    refine ⟨max t (max cr.gst (max cr.tr s)) + cr.delay - t, fun b hb => ?_⟩
    have := h (cr.holds_mono w t _ (le_max_left _ _) hb)
    rwa [show t + (max t (max cr.gst (max cr.tr s)) + cr.delay - t) =
      max t (max cr.gst (max cr.tr s)) + cr.delay by omega]
  advancesAt := cr.advancesAt

end Scheme

end LeanDag
