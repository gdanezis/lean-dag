import LeanDag.BlackMarlin.Model.Order
import LeanDag.BlackMarlin.Model.Descent
/-!
# Black Marlin — `commit(B)` as the paper writes it

`Flush` models a validator's boundaries as a function of round, and
`ledgerSeq` reads them off in round order; Algorithm 1 is narrower —
`commit(B)` recurses into the undelivered anchors of `strong(B)` afresh
at each successful `delivery(r)`, threading the delivered set `D` across
invocations (`black-marlin.md` §16). The two differ where a later commit
descends below a boundary an earlier one already passed, which a
round-indexed record cannot express; this file writes the recursion
directly so the abstraction can be checked against it.

**L30 is outside L27's filter.** Read literally, the anchor `B` is
delivered whatever `D` holds, so a validator that committed one twin and
later descends to the other delivers both — Integrity, outright. §4.4's
prose says otherwise ("only the first block ... is ab-delivered"), and
`commitSeq` takes the prose, filtering `B` as well.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **L21–L24 against the delivered set** (L19): the choice is made among
the anchors of `strong(B) \ D`, where `descend` takes all of
`strong(B)`. The metric of L24 is unchanged, reading `strong(A)` in
full. -/
def descendD (U : BlockUniverse Validator BlockId Payload) (B : BlockId)
    (D : Finset BlockId) : Option BlockId :=
  pick ((maxAnchor U (strongOf U B \ D)).filter
    (fun X => ∀ C ∈ maxAnchor U (strongOf U B \ D), anchorGap U X ≤ anchorGap U C))

/-- **L27's test**: some delivered block shares this one's author and
round. -/
def keyHeld (U : BlockUniverse Validator BlockId Payload) (b : BlockId)
    (D : Finset BlockId) : Prop :=
  ∃ c ∈ D, key U c = key U b

instance (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (D : Finset BlockId) :
    Decidable (keyHeld U b D) :=
  inferInstanceAs (Decidable (∃ _ ∈ D, _ = _))

/-- **L26–L29**: emit a sorted segment, dropping any block whose author
and round have already gone out, and threading `D`. -/
def emitFrom (U : BlockUniverse Validator BlockId Payload) :
    List BlockId → Finset BlockId → List BlockId × Finset BlockId
  | [], D => ([], D)
  | b :: bs, D =>
      if keyHeld U b D then emitFrom U bs D
      else
        let r := emitFrom U bs (insert b D)
        (b :: r.1, r.2)

/-- **L18–L32**, with fuel for the recursion: descend first, then emit
`τ(past(B) \ D)`, then `B` itself. Returns what the invocation
`ab-deliver`s and the delivered set it leaves behind, so successive
invocations compose. -/
def commitSeq (U : BlockUniverse Validator BlockId Payload) (τ : TopoSort U) :
    ℕ → BlockId → Finset BlockId → List BlockId × Finset BlockId
  | 0, B, D => ([], insert B D)
  | (n + 1), B, D =>
      let pd :=
        match descendD U B D with
        | none => (([] : List BlockId), D)
        | some B' => commitSeq U τ n B' D
      let md := emitFrom U (τ.sort ((history U B).erase B \ pd.2)) pd.2
      (pd.1 ++ md.1 ++ (if keyHeld U B md.2 then [] else [B]), insert B md.2)

end BlackMarlin

end LeanDag
