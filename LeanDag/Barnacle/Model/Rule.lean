import LeanDag.Mysticeti.Rule
import LeanDag.Common.Causality
import LeanDag.Properties.Carrier
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
/-!
# Barnacle: the base-protocol interface

The paper abstracts the protocol it runs on as four assumptions, A1–A4
(`barnacle.md` §2): rounds and slots, causal completeness, a
direct decision predicate, and safety and liveness for every fixed
configuration. `BaseRule` is that abstraction as a Lean structure — its
data — and `BaseRule.Laws` the proposition the data must satisfy. The
arc never counts anything and never inspects a quorum: the leader-count
mechanism is stated over an arbitrary `BaseRule` satisfying `Laws`, and
the eight commit rules of this development are each shown to, as a
result with a `Statement` and a `Proof` — through `ofAnchored`
(`Model/Anchored.lean`), which reads a base rule off any anchored rule,
and whose laws are proved once (`Helpers/Anchored.lean`).

The universe and view types are *fields*, bundled in `Type`, because
the rules do not share them: the Byzantine rules use `BlockUniverse`
and `View`, the crash rule its own `Nemo.Universe` and `Nemo.View`, and
the hybrid rule the subtype of universes satisfying `HonestNoEquiv`.
Bundling puts each rule's fault class on its instantiation and nothing
on the interface, which is what lets Nemo — whose safety needs no fault
class at all — instantiate it without one, and Orcaella carry a
hypothesis the interface has no slot for.

The schedule is an explicit argument of `Decided` rather than an
instance: the arc's whole subject is several `Slots` instances on one
validator type, one per configuration, and every use names its schedule.

Liveness is not here. What the paper's A4 asks of a fixed configuration
beyond agreement is stated in Phase 3 as a clause on a schedule, over a
structure extending this one, so that this file is not reopened.

**Trusted core of the arc: definitions only.** No theorem and no proof
term lives in this file; the `Decidable` instances are definitions by
`inferInstanceAs` or field projections and carry no proof content. Results are stated in
`<Result>/Statement.lean` files and proved in their `Proof.lean`
(`barnacle.md` §10).
-/

namespace LeanDag

namespace Barnacle

/-- **The base protocol, as the paper assumes it — the data.** A universe
of blocks with its views, the direct decision predicate, and a decision
relation parametric in the schedule. The laws these must satisfy are
`BaseRule.Laws` below, a proposition each instantiation is proved to
meet in its own `Statement`/`Proof` pair.

`historyView` is the view a validator measures on — the anchor's causal
history, which the paper's `GetSubDag` computes. An instantiation may
build it however it likes: the law `historyView_ids` pins its ids to
`historyFrom`, the shared history function of `Causality.lean`, so that
the window is a function of the universe and the anchor alone. -/
structure BaseRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    extends Properties.DagRule Validator BlockId Payload where
  /-- The full view: every block of the universe. -/
  full : ∀ U : Universe, View U
  /-- The causal history of a block of the universe, as a view. -/
  historyView : ∀ (U : Universe) (A : BlockId), A ∈ ids U → View U
  /-- **A3.** The length of a wave: the rounds the direct rule reads from a
  slot's proposal. Three for Mysticeti, two for the two-round rules. -/
  waveLength : ℕ
  /-- **A3.** The direct commit predicate, as judged from a view: block `L`
  proposed at round `r` is directly committed. -/
  DirectCommitIn : ∀ {U : Universe}, View U → BlockId → ℕ → Prop
  /-- The direct predicate is decidable, so a validator — and a witness —
  can compute the window count. -/
  decDirect : ∀ {U : Universe} (V : View U) (L : BlockId) (r : ℕ),
    Decidable (DirectCommitIn V L r)

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

namespace BaseRule

/-- The rule's own decidability of the direct predicate, as an instance. -/
instance instDecidableDirectCommitIn (R : BaseRule Validator BlockId Payload)
    {U : R.Universe} (V : R.View U) (L : BlockId) (r : ℕ) :
    Decidable (R.DirectCommitIn V L r) :=
  R.decDirect V L r

/-- `L` is a candidate block for slot `k` of schedule `S`: the right round,
the right author. The same conjunction every rule of this development
states, here over the interface's `block` and `ids` so that the arc has
one candidate predicate for all four. -/
def IsLeaderBlock (R : BaseRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ R.ids U ∧ (R.block U L).round = S.slotRound k ∧ (R.block U L).creator = S.leader k

instance instDecidableIsLeaderBlock (R : BaseRule Validator BlockId Payload)
    (S : Slots Validator) (U : R.Universe) (k : ℕ) (L : BlockId) :
    Decidable (R.IsLeaderBlock S U k L) :=
  inferInstanceAs (Decidable (L ∈ R.ids U ∧ (R.block U L).round = S.slotRound k ∧
    (R.block U L).creator = S.leader k))

/-- **A view caught up to round `N`**: it holds every block of the
universe at a round at or below `N`. This is what a validator that has
received everything up to `N` holds, and the condition under which the
liveness results hold of its own view rather than of the whole
universe. The full view satisfies it at every `N`. -/
def CoversUpto (R : BaseRule Validator BlockId Payload) (U : R.Universe)
    (V : R.View U) (N : ℕ) : Prop :=
  ∀ b ∈ R.ids U, (R.block U b).round ≤ N → b ∈ R.viewIds V

/-- **The laws of a base rule** — what the leader-count mechanism
consumes of the protocol, and what each instantiation is proved to
satisfy. A2 — a validator holds a block only with its whole causal
history — is carried by `BaseRule` itself, as the fields `viewSound`
and `viewComplete`. Two laws pin the two view fields: the full view is
the universe, the history view is the history. The other three are the
properties of `docs/target-properties.md`, read at the rule's carrier:
`agree` is the safety half of A4 (for a fixed schedule, verdicts agree
across views); `commitsDirect` ties the direct predicate to the
relation, which is what makes the window count a count of *verdicts*:
two directly committed candidates of one slot are one block, by
`agree`; `candidates` is its converse, a committed block is a candidate
of its slot. The liveness half of A4 is stated in Phase 3 over an
extension of the data.

Every anchored rule with its laws has these, once
(`Helpers/Anchored.lean`): the view laws by construction, the three
properties from `Common/Anchored/Band.lean`. -/
structure Laws (R : BaseRule Validator BlockId Payload) : Prop where
  /-- The full view holds exactly the universe. -/
  full_ids : ∀ U, R.viewIds (R.full U) = R.ids U
  /-- The history view holds exactly the history. -/
  historyView_ids : ∀ U A (hA : A ∈ R.ids U),
    R.viewIds (R.historyView U A hA) = historyFrom (R.block U) A
  /-- **A4, safety.** For a fixed schedule, verdicts agree across views. -/
  agree : Properties.Agree R.toDagRule
  /-- A directly committed candidate of a slot is a commit verdict. -/
  commitsDirect : Properties.CommitsDirect R.toDagRule (fun {U} V L r => R.DirectCommitIn V L r)
  /-- A committed block is a candidate of its slot: the right round, the
  right author. The other half of "verdicts are about candidates", and
  what makes a block appear at most once in the ledger. -/
  candidates : Properties.CommitsCandidate R.toDagRule

end BaseRule

/-- **An update rule**: from the current leader count and back-off, the
universe and the anchor block, the next count and back-off. Safety is
stated for every such function (`barnacle.md` §1); the paper's
AIMD rule is one instance (`Model/Window.lean`). -/
abbrev UpdateRule (R : BaseRule Validator BlockId Payload) : Type :=
  ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ

/-- **A rule a validator can run without disagreeing.** The step depends
on the count, the back-off and the anchor, and on the *view* only through
what every view holding the anchor shares.

The type above lets a rule read the view, which is what a validator
actually has. Nothing then makes two validators agree, and nothing
should: a rule reading its own view freely could return different counts
to two correct validators and break the configuration sequence outright.
`Anchored` is the condition that rules that out, and it is not a
restriction in practice — the window a rule measures on is the anchor's
causal history, which BN2 shows every view holding the anchor holds
whole and restricts identically. A rule computing from its own copy of
that history satisfies this; the AIMD rule of `Model/Window.lean` does,
by not reading the view at all. -/
def Anchored (R : BaseRule Validator BlockId Payload) (upd : UpdateRule R) : Prop :=
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (m b : ℕ) (A : BlockId),
    upd m b U V₁ A = upd m b U V₂ A

end Barnacle

end LeanDag
