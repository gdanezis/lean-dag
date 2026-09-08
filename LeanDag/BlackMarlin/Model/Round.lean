import LeanDag.BlackMarlin.Model.Decision
import LeanDag.Mysticeti.ViewPace
/-!
# Black Marlin — the round rule, and the pace it induces

Algorithm 1's `quorum`, `anchor` and `suppAnchor`, and Algorithm 2's
L38–L41 (`black-marlin.md` §9). A validator concludes round `r` when it
holds a quorum of authors at `r`, holds the anchor of `r`, and sees the
two anchors below `r` supported — or when the round's timeout fires, the
dual condition that makes the protocol responsive: it runs at the actual
delivery time rather than at `∆`, without deadlocking when an anchor is
Byzantine.

The two lower clauses are stated additively — `∀ ρ, ρ + 1 = r → …` and
`∀ ρ, ρ + 2 = r → …` rather than truncated subtraction — so the first
two rounds are vacuous rather than a separate branch, as `ValidWrt`
treats genesis. `Pace` extends the core's `PaceCore`, inheriting the
views, convergence, progress and production; new is `anchor_or_wait`,
the round rule on a produced block, and `prompt_conclude`, bounding the
reactive exit. `prompt_conclude` is where this differs from the core's
`ReactivePace`: its exit fires once the leader's block is held, this
one's once the validator can conclude the round — three further
clauses, measured in `Reactive/Statement.lean` as a run of three
reliable anchors to enter, against the commit rule's two.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **`quorum(r)`**, as the validator computes it: blocks from at least
`n − f` distinct authors at round `r` among what the view holds. -/
def QuorumIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (authorsIn U V.ids r).card

instance {V : View Validator BlockId Payload U} (r : ℕ) : Decidable (QuorumIn U V r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **`anchor(r)`**: the view holds a block by the validator the rotation
elected for round `r`. -/
def AnchorIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (r : ℕ) : Prop :=
  ∃ A ∈ V.ids, IsAnchor U r A

instance {V : View Validator BlockId Payload U} (r : ℕ) : Decidable (AnchorIn U V r) :=
  inferInstanceAs (Decidable (∃ A ∈ V.ids, IsAnchor U r A))

/-- **`suppAnchor(r)`**: the view holds an anchor of round `r` carrying a
quorum of support, counted among the round-`(r+1)` blocks the view
holds. The same `SupportedIn` the commit rule reads, which is why the
round rule and the commit rule share their arithmetic. -/
def SuppAnchorIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (r : ℕ) : Prop :=
  ∃ A, IsAnchor U r A ∧ SupportedIn U V A r

/-- Decidable on a finite identifier type, which is what a concrete model
supplies. The two lower clauses of `ConcludesAt` quantify over every `ρ`
below the round, so the rule itself is not decidable and a witness
discharges them by `omega` and `decide` together. -/
instance {V : View Validator BlockId Payload U} (r : ℕ) [Fintype BlockId] :
    Decidable (SuppAnchorIn U V r) :=
  inferInstanceAs (Decidable (∃ A, IsAnchor U r A ∧ SupportedIn U V A r))

/-- **The round rule** (L40, first disjunct): what a validator must see
before it may conclude round `r` without waiting out the timeout. -/
def ConcludesAt (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (r : ℕ) : Prop :=
  QuorumIn U V r ∧ AnchorIn U V r ∧
    (∀ ρ, ρ + 1 = r → SuppAnchorIn U V ρ) ∧
    (∀ ρ, ρ + 2 = r → SuppAnchorIn U V ρ)

/-- **The Black Marlin pacing structure**: the core's `PaceCore` with the
reactive discipline of L38–L41 in place of the full-timeout one — no
validator waits past its timeout, and the full-timeout floor is
absent. -/
structure Pace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends PaceCore U T N where
  /-- Time advances with rounds, over the rounds `v` reached. -/
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- **The ceiling.** A validator never waits past the round's timeout;
  it may build any time before it. -/
  deadline : ∀ v ∈ T, ∀ n < top v, built v (n + 1) ≤ built v n + timeout n
  /-- **The anchor wait**, the round rule read on the block a validator
  produces. At the round above a reliable anchor, a `T`-authored block
  either references it — the exit fired, requiring it — or waited the
  full timeout and would have referenced it had it held it. Stated only
  where the round's elected validator lies in `T`: for a Byzantine
  anchor it may equivocate, and nothing useful can be said. -/
  anchor_or_wait : ∀ v ∈ T, ∀ r, r + 1 ≤ N → Rot.anchor r ∈ T →
    ∀ A, IsAnchor U r A →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = r + 1 →
    A ∈ (U.block c).refs ∨
      (built v r + timeout r ≤ built v (r + 1) ∧
        (A ∈ holds v (built v (r + 1)) → A ∈ (U.block c).refs))
  /-- **The exit is prompt.** A validator past its round entry that can
  conclude the round does so within the processing bound — the whole of
  `ConcludesAt`, where the core's `ReactivePace.prompt_vote` asks only
  that the leader's block be held. -/
  prompt_conclude : ∀ v ∈ T, ∀ r, r + 1 ≤ N → ∀ t, built v r ≤ t →
    ConcludesAt U (toPaceCore.viewAt v t) r →
    built v (r + 1) ≤ t + proc

end BlackMarlin

end LeanDag
