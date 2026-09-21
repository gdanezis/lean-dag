import LeanDag.RedSnapper.Model.Votes
import LeanDag.RedSnapper.Model.Certificates

/-!
# The 5f+1 certificates

Trusted core: the four threshold objects of §8 ("Certificates and
voting", `Alg:FastPathPredicates5f+1`) — the full certificate, the half
certificate, the refutation, and the full unlock certificate — over the
unchanged Phase 3 model: the same blocks, stances and universe, the
same `AtLeast` counting over round parents, the D1 thresholds (`quorum`
for the paper's `4f+1`, `half` for its `2f+1`).

An *anti-vote* against a stance value `s` is a block whose author
stands at some other value — `⊥` or a rival ACK against an ACK (any
other ACK on the one input is a rival under D2), any ACK against `⊥` —
and `none` contributes nothing. A *refutation* of `s` is `half`
anti-votes among a block's parents: the observed evidence that `s` can
no longer complete a quorum, RS1's revocation threshold in DAG form.
The refutation of `⊥` may be **split** across rival transactions — the
algorithm's rule, which the text of Lemma unlock-excludes-half
misstates as a half certificate (`docs/red-snapper.md` §3, finding 8).

Unlike the `3f+1` certificate, the full certificate has **no own-vote
clause** — §8 counts the parents alone — and the full unlock
certificate has **no conflict clause** — §8's unlock vote is bare `⊥`,
where §7's carried the recovery gate.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- `b` is an anti-vote against the stance value `s` on `o` (the paper's
`IsAntiVoteObj`): its author stands at some other value. A stance of
`none` is neither a vote nor an anti-vote. -/
def IsAntiVote (U : Universe Validator BlockId Tx Obj) (b : BlockId) (o : Obj)
    (s : Stance Tx) : Prop :=
  ∃ s', StanceIs U (U.block b).author o b (some s') ∧ s' ≠ s

/-- `C` carries a full certificate for `tx` (the paper's
`IsFullCertTX`): a quorum of its parents are fast votes. Finality in one
observation. -/
def IsFullCert (U : Universe Validator BlockId Tx Obj) (C : BlockId) (tx : Tx) : Prop :=
  AtLeast U (quorum Validator) (U.block C).parents fun b => IsFastVote U b tx

/-- `C` carries a half certificate for `tx` (the paper's
`IsHalfCertTX`): `half` of its parents are fast votes — enough that no
conflicting transaction can ever reach a full certificate. -/
def IsHalfCert (U : Universe Validator BlockId Tx Obj) (C : BlockId) (tx : Tx) : Prop :=
  AtLeast U (half Validator) (U.block C).parents fun b => IsFastVote U b tx

/-- `C` carries a refutation of the stance value `s` on `o` (the paper's
`IsRefutation`): `half` of its parents are anti-votes against `s` —
after which `s` cannot have completed a quorum, and its holder may
safely move. -/
def IsRefutation (U : Universe Validator BlockId Tx Obj) (C : BlockId) (o : Obj)
    (s : Stance Tx) : Prop :=
  AtLeast U (half Validator) (U.block C).parents fun b => IsAntiVote U b o s

/-- `C` carries a full unlock certificate for `o` (the paper's
`IsFullUnlockCertObj`): a quorum of its parents stand at `⊥`. The
object is released without committing anything. -/
def IsFullUnlockCert (U : Universe Validator BlockId Tx Obj) (C : BlockId) (o : Obj) :
    Prop :=
  AtLeast U (quorum Validator) (U.block C).parents fun b =>
    StanceIs U (U.block b).author o b (some Stance.bot)

end RedSnapper

end LeanDag
