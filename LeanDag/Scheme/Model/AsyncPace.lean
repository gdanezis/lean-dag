import LeanDag.Mysticeti.ViewPace
import LeanDag.Scheme.Model.Rule
/-!
# The family, paced asynchronously

`docs/scheme.md` §11.1. The pacing that asynchronous liveness rests on has
no clock: no GST, no delay bound, no timeout. A validator's holdings grow,
are causally closed, and include its own blocks once built; whatever one
reliable validator holds, every reliable validator holds at some later
time (`ConvergesEventually`, the untimed half of the trunk's `converges`);
and a reliable validator holding `q` distinct round-`n` authors gets past
round `n`. The quorum `q` is a parameter, so the hybrid committees are
covered as well.

`AsyncPace.viewAt v hv t` is a reliable validator's own view at time `t`:
its holdings, a view because they are causally closed.
`AsyncPace.Eventually Φ` says every reliable validator's own view
satisfies `Φ` from some time on; `AsyncPace.EventuallyCommits` says so of
one leader block of a slot being committed. On a single view,
`WindowsCommit` says every window of `c` slots below the horizon has a
committed slot, and `PrefixDecided` that every slot below some point past
each window is decided.

Definitions only; the claims are `Scheme/AsyncLocal/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **Asynchronous pacing** at quorum `q`, over a horizon `N`: holdings that
converge eventually, and the pacemaker's progress rule at `q`. -/
structure AsyncPace (q : ℕ) (U : BlockRecord Validator BlockId Payload P honest)
    (T : Finset Validator) (N : ℕ) where
  /-- The highest round `v` reached. -/
  top : Validator → ℕ
  /-- Every round a reliable validator reached, it built in. -/
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  /-- What `v` holds at time `t`. -/
  holds : Validator → ℕ → Finset BlockId
  /-- A validator holds only blocks that exist. -/
  holds_sub : ∀ v, ∀ t, holds v t ⊆ U.ids
  /-- A reliable validator's holdings are causally closed. -/
  holds_closed : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t, ∀ j ∈ (U.block b).refs, j ∈ holds v t
  /-- Holdings only grow. -/
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- A reliable validator holds each block it authored, from some time on. -/
  holds_own : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v → ∃ t, b ∈ holds v t
  /-- **Eventual delivery** among the reliable validators. -/
  converges : ConvergesEventually holds T
  /-- **The progress rule at `q`.** A reliable validator holding `q`
  distinct round-`n` authors gets past round `n`. -/
  advancesAt : ∀ v ∈ T, ∀ n < N, ∀ t, q ≤ (authorsIn U (holds v t) n).card → n < top v

namespace AsyncPace

variable {q N : ℕ} {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator}

/-- **A reliable validator's view at time `t`**: its holdings. -/
def viewAt (ap : AsyncPace q U T N) {v : Validator} (hv : v ∈ T) (t : ℕ) : U.View where
  ids := ap.holds v t
  subset_ids := ap.holds_sub v t
  complete := ap.holds_closed v hv t

/-- **From some time on, every reliable validator's own view satisfies
`Φ`.** -/
abbrev Eventually (ap : AsyncPace q U T N) (Φ : U.View → Prop) : Prop :=
  ∃ t, ∀ t', t ≤ t' → ∀ v (hv : v ∈ T), Φ (ap.viewAt hv t')

/-- **Slot `k` eventually commits on every reliable validator's own view**:
one leader block of the slot is decided on each such view from some time
on. -/
def EventuallyCommits (ap : AsyncPace q U T N) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator] (k : ℕ) : Prop :=
  ∃ L, IsLeaderBlock U k L ∧ ap.Eventually fun V => (schemeAnchored p σ).Decided U V k (some L)

/-- **A timed run is an asynchronous one**: the trunk of every timed
discipline, with a progress rule at `q`, forgets its clock. -/
def ofPaceCore [Faults Validator] (pc : PaceCore U T N)
    (hadv : ∀ v ∈ T, ∀ n < N, ∀ t, q ≤ (authorsIn U (pc.holds v t) n).card → n < pc.top v) :
    AsyncPace q U T N where
  top := pc.top
  built_of_le_top := pc.built_of_le_top
  holds := pc.holds
  holds_sub := pc.holds_sub
  holds_closed := pc.holds_closed
  holds_mono := pc.holds_mono
  holds_own := fun v hv b hb hbc =>
    ⟨_, pc.holds_own v hv _ (pc.rounds_le b hb) b hb hbc rfl⟩
  converges := convergesEventually_of_within pc.holds_mono pc.converges
  advancesAt := hadv

end AsyncPace

variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]

/-- **Every window commits on the view `V`**: in every window of `c` slots
whose decision rounds lie below the horizon `N`, some slot's leader block
is committed on `V`. -/
def WindowsCommit (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (c N : ℕ) : Prop :=
  ∀ k, (schemeAnchored p σ).decisionRound (k + c) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∃ L, IsLeaderBlock U k' L ∧
      (schemeAnchored p σ).Decided U V k' (some L)

/-- **The decided prefix of the view `V` keeps up with the horizon**: for
every slot `k` whose window of `c` slots and run of `d` lie below `N`,
every slot below some `b ≥ k` is decided on `V`. -/
def PrefixDecided (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (c d N : ℕ) : Prop :=
  ∀ k, (schemeAnchored p σ).decisionRound (k + c + d - 1) ≤ N →
    ∃ b, k ≤ b ∧ ∀ i < b, ∃ w, (schemeAnchored p σ).Decided U V i w

end Scheme

end LeanDag
