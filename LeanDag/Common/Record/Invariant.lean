import LeanDag.Common.Record.Chop
import LeanDag.Common.Record.Fill
import LeanDag.Common.Record.Genesis
/-!
# Invariants a carrier adds to the record

Orcaella's universes are the core's records under `HonestNoEquiv`;
Optimal-Hydrozoan's are Hydrozoan's under leader exclusion. Such a
carrier gets the mechanisms once its invariant is shown to survive them:
the cut, the copy fill and re-genesis. The general fill is read by
`DagRule.OnRecord.fill` with the invariant supplied by hand, since a
reading of the filled blocks other than the copy is the rule's own.
`Any` is the trivial invariant of a carrier that adds nothing.
-/

namespace LeanDag

namespace BlockRecord

variable {Validator : Type*} {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- The trivial invariant. -/
def Any (_ : BlockRecord Validator BlockId Payload P honest) : Prop := True

/-- **What an invariant owes the cut.** -/
class Invariant.Chops [P.Mechanised]
    (I : BlockRecord Validator BlockId Payload P honest → Prop) : Prop where
  /-- It survives the cut. -/
  chop : ∀ {W : BlockRecord Validator BlockId Payload P honest} (G : ℕ), I W → I (W.chop G)

/-- **What an invariant owes re-genesis.** -/
class Invariant.Regenesis [P.Mechanised]
    (I : BlockRecord Validator BlockId Payload P honest → Prop) : Prop where
  /-- It survives re-genesis. -/
  addGenesis : ∀ {W : BlockRecord Validator BlockId Payload P honest} (v : Validator)
    (g : BlockId) (p : Payload) (hg : g ∉ W.ids) (hsev : ∀ b ∈ W.ids, (W.block b).creator ≠ v),
    I W → I (W.addGenesis v g p hg hsev)

/-- **What an invariant owes the mechanisms.** -/
class Invariant.Mechanised [P.Mechanised]
    (I : BlockRecord Validator BlockId Payload P honest → Prop) : Prop
    extends Invariant.Chops I, Invariant.Regenesis I where
  /-- It survives the copy fill. -/
  copyFill : ∀ [P.CopyStable] {W : BlockRecord Validator BlockId Payload P honest}
    (sk : SkipData W.ids W.block), I W → I (BlockRecord.copyFill W sk)

instance [P.Mechanised] : Invariant.Mechanised (Any (P := P) (honest := honest)) where
  chop := fun _ _ => True.intro
  copyFill := fun _ _ => True.intro
  addGenesis := fun _ _ _ _ _ _ => True.intro

end BlockRecord

end LeanDag
