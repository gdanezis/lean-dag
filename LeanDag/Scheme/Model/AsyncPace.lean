import LeanDag.Mysticeti.ViewPace
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

end Scheme

end LeanDag
