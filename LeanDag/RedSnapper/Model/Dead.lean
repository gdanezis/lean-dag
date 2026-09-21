import LeanDag.RedSnapper.Model.Certificates
import LeanDag.RedSnapper.Model.Anchors

/-!
# Death, release readiness, and resolution

Trusted core: the paper's `Dead` and `Resolves`
(`Alg:FastPathPredicates`), the predicates behind the anchor routes.

A transaction is *dead* at a block when some evidence there decides its
input against it: a conflicting transaction certified in the causal
history, a skip certificate for its input there, or the input *released*
at an earlier committed anchor. An anchor is *release-ready* for an
object when the object is conflicted there, every candidate certified in
its history is dead, and a skip or unlock certificate for the object
lies in its history — the three conditions of the paper's `Resolves` —
and the object *resolves* at the first ready anchor (the paper's
one-shot clause).

The paper's `Dead` and `Resolves` are mutually recursive through the
committed order. The arc renders the recursion structurally (the plan's
one design novelty): `DeadGiven` and `ResolveReadyGiven` take the
already-released set as a parameter `R : Obj → Prop` and are
non-recursive transcriptions of the paper's clauses; `ReleasedBelow`
then recurses on the anchor *index* alone — nothing is released below
index `0`, and below `i + 1` an object is released below `i` or anchor
`i` is ready for it given what is released below `i`. `ResolveReadyAt`,
`ResolvesAt` and `DeadAt` read the paper's predicates back off this at
each index; that `ReleasedBelow i` coincides with "some anchor below `i`
is ready" is proved in `Helpers/`, not assumed.

Two fidelity notes. The paper's `Dead` reads the *strict* history
(`b' ≠ b`) so that `CastVotes` can evaluate it while writing `b`; here
the reflexive `HasCert`/`Reaches` are used. The two differ exactly when
the anchor itself is the certificate or skip certificate, and no anchor
verdict changes under the stance discipline: each divergence scenario
needs two certificates for one object or a skip certificate beside an
ack certificate, both excluded by RS2. The liveness phase, where the
strictness matters, states its own form. And "an earlier anchor" is the
committed order (indices), the paper's `Link(A, b)` reading being
equivalent through `Anchors.chained`
(`docs/red-snapper.md` §3, finding 3).
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- `tx` is dead at block `a`, given `R` as the already-released objects
(the paper's `Dead`, clause for clause): a conflicting transaction is
certified in `a`'s history, or a skip certificate for `tx`'s input lies
there — an unlock certificate is bivalent and never witnesses death — or
the input is released. -/
def DeadGiven (U : Universe Validator BlockId Tx Obj) (a : BlockId) (R : Obj → Prop)
    (tx : Tx) : Prop :=
  (∃ tx', Conflict tx tx' ∧ HasCert U a tx') ∨
    (∃ C ∈ U.ids, IsSkipCert U C (T.input tx) ∧ Reaches U a C) ∨
    R (T.input tx)

/-- Block `a` is release-ready for `o`, given `R` as the already-released
objects — the three conditions of the paper's `Resolves`: the object is
conflicted at `a`, no candidate certified in `a`'s history is alive, and
a skip or unlock certificate for `o` lies in `a`'s history. -/
def ResolveReadyGiven (U : Universe Validator BlockId Tx Obj) (a : BlockId)
    (R : Obj → Prop) (o : Obj) : Prop :=
  Conflicted U a o ∧
    (∀ tx, IsCandidate U a o tx → HasCert U a tx → DeadGiven U a R tx) ∧
    (∃ C ∈ U.ids, (IsSkipCert U C o ∨ IsUnlockCert U C o) ∧ Reaches U a C)

/-- `o` is released at some anchor strictly below index `i`: below `0`
nothing is; below `i + 1`, either below `i`, or anchor `i` is
release-ready for `o` given what is released below `i`. -/
def ReleasedBelow (U : Universe Validator BlockId Tx Obj) (A : Anchors U) :
    ℕ → Obj → Prop
  | 0, _ => False
  | i + 1, o => ReleasedBelow U A i o ∨
      ∃ a, A.seq[i]? = some a ∧ ResolveReadyGiven U a (ReleasedBelow U A i) o

/-- Anchor `i` is release-ready for `o`. -/
def ResolveReadyAt (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (i : ℕ)
    (o : Obj) : Prop :=
  ∃ a, A.seq[i]? = some a ∧ ResolveReadyGiven U a (ReleasedBelow U A i) o

/-- `o` resolves at anchor `i` (the paper's `Resolves`): the first
release-ready anchor — one-shot, as the paper's last clause demands. -/
def ResolvesAt (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (i : ℕ)
    (o : Obj) : Prop :=
  ResolveReadyAt U A i o ∧ ∀ j < i, ¬ ResolveReadyAt U A j o

/-- `tx` is dead at anchor `i` (the paper's `Dead`, at an anchor). -/
def DeadAt (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (i : ℕ)
    (tx : Tx) : Prop :=
  ∃ a, A.seq[i]? = some a ∧ DeadGiven U a (ReleasedBelow U A i) tx

end RedSnapper

end LeanDag
