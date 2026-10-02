import LeanDag.RedSnapper.Model.CausalHistory

/-!
# The committed anchors

Trusted core: the consensus interface of the paper's Preliminaries
("Consensus Interface", (C1)–(C4)), as one global object (D4 of
`docs/red-snapper.md`).

The fast path treats consensus as a black box that outputs a totally
ordered, append-only sequence of committed anchor blocks, identical at
every correct validator, with each anchor's causal history determined by
its parents closure. (C1)–(C3) are therefore not hypotheses here but the
fact that `Anchors` is a single value: every verdict the anchor routes
derive is a function of `(U, A)` and agreement across validators about
them is definitional. A validator that has processed only a prefix of
the sequence derives a subset of the verdicts, never a different one,
because every anchor-indexed clause of the decision layer looks only
downward in the order. (C4) — anchors keep coming — is a liveness
hypothesis of a later phase.

The sequence is **chained**: every earlier anchor lies in the causal
history of every later one. This is the property of Mysticeti's commit
rule that the paper's `Dead` and `Spendable` assume when they test an
earlier anchor with `Link(A, b)` while the proofs argue by committed
order (`docs/red-snapper.md` §3, finding 3); the arc states it once,
here. It is what makes visible conflicts, certificates and release
evidence monotone along the committed order.
-/

namespace LeanDag

namespace RedSnapper

/-- The committed anchor sequence: a global, totally ordered list of
blocks of the universe, chained through causal history. -/
structure Anchors {Validator BlockId Tx Obj : Type*} [Fintype Validator]
    [DecidableEq Validator] [F : Faults Validator]
    (U : Universe Validator BlockId Tx Obj) where
  /-- The committed anchors, in committed order. -/
  seq : List BlockId
  /-- Every anchor is a block of the universe. -/
  mem : ∀ a ∈ seq, a ∈ U.ids
  /-- Every earlier anchor lies in the causal history of every later
  one. -/
  chained : seq.Pairwise fun earlier later => Reaches U later earlier

end RedSnapper

end LeanDag
