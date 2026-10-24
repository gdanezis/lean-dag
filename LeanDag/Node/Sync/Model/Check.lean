import LeanDag.Node.Sync.Model.Stream
/-!
# Sync by causal streams — the checks

`docs/sync.md` §3. A block carries evidence: pairs of identifiers it names
as twins, read from its payload by `ev`. A block exposes `X` when its
history holds a block carrying evidence against `X` (`Exposes`). A block passes the checks when its references sit one round
below it, name a quorum of `n − f` authors unless it is at round `0`, and
name no author it exposes (`Checks`). A target is admitted when every block
of its history passes them (`Admits`): a pass over the headers before the
stream. The authors a set of blocks catches are those with twins in it and
those its blocks carry evidence against (`caught`).

Definitions only.
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable (blk : BlockId → Block Validator BlockId Payload)
variable (ev : Payload → Finset (BlockId × BlockId))

/-- **`b` carries evidence against `X`**: a pair of twins by `X` named in its
payload. -/
def Convicts (b : BlockId) (X : Validator) : Prop :=
  ∃ p ∈ ev (blk b).payload, Twins blk p.1 p.2 ∧ (blk p.1).creator = X

instance (b : BlockId) (X : Validator) : Decidable (Convicts blk ev b X) :=
  inferInstanceAs (Decidable (∃ p ∈ ev (blk b).payload, _))

/-- **`b` exposes `X`**: `b`'s history holds a block carrying evidence
against `X`. -/
def Exposes (b : BlockId) (X : Validator) : Prop :=
  ∃ i ∈ historyFrom blk b, Convicts blk ev i X

instance (b : BlockId) (X : Validator) : Decidable (Exposes blk ev b X) :=
  inferInstanceAs (Decidable (∃ i ∈ historyFrom blk b, _))

variable [Fintype Validator] (f : ℕ)

/-- **The checks a block passes**: its references sit one round below it,
name a quorum of `n − f` authors unless it is at round `0`, and name no
author it exposes. -/
def Checks (b : BlockId) : Prop :=
  (∀ j ∈ (blk b).refs, (blk j).round + 1 = (blk b).round) ∧
    (0 < (blk b).round → Fintype.card Validator - f ≤ (creatorsOf blk (blk b).refs).card) ∧
    ∀ j ∈ (blk b).refs, ¬ Exposes blk ev b (blk j).creator

instance (b : BlockId) : Decidable (Checks blk ev f b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A target is admitted** when every block of its history passes the
checks. -/
def Admits (t : BlockId) : Prop :=
  ∀ i ∈ historyFrom blk t, Checks blk ev f i

instance (t : BlockId) : Decidable (Admits blk ev f t) :=
  inferInstanceAs (Decidable (∀ i ∈ historyFrom blk t, _))

/-- **The authors `S` catches**: those with twins in `S`, and those a block
of `S` carries evidence against. -/
def caught (S : Finset BlockId) : Finset Validator :=
  ((S.filter fun i => ∃ j ∈ S, Twins blk i j).image fun i => (blk i).creator) ∪
    S.biUnion fun i =>
      ((ev (blk i).payload).filter fun p => Twins blk p.1 p.2).image fun p => (blk p.1).creator

end Sync

end Node

end LeanDag
