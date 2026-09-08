import LeanDag.BlackMarlin.Model.Rules
/-!
# Black Marlin — the rule as a validator applies it

`black-marlin.md` §3. A validator runs `delivery(r)` against its own
`DAG`, so every count of `Rules.lean` is here intersected against a
view.

There is no separate decision relation: Black Marlin has no skip verdict
and no indirect rule, since an anchor the rule does not admit is simply
delivered, in its turn, inside a later admitted anchor's causal history.
So the whole of what a validator decides is `CommittedIn`, and agreement
is the statement that two validators' committed anchors lie on one chain
(`Safety/Statement.lean`).

A view under-reports, so each count it takes is at most the universe's —
the one direction safety needs, established in `Helpers/Decision.lean`.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- `supp(L) ≥ n − f`, counted in a view: the record's `supportersIn`. -/
def SupportedIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supportersIn U V L (r + 1)).card

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable (SupportedIn U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The linking anchors a view holds, each supported within that same
view. Both the linking block and the quorum behind it must be present:
`delivery(r)` reads one `DAG`, and a validator cannot count support it
has not received. -/
def linkersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  ((blocksAt U (r + 1)).filter
    (fun L' => (U.block L').creator = Rot.anchor (r + 1) ∧ L ∈ (U.block L').refs ∧
      SupportedIn U V L' (r + 1))) ∩ V.ids

/-- `L` is linked, as judged from a view. -/
def LinkedIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (linkersIn U V L r).Nonempty

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable (LinkedIn U V L r) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

/-- **The commit rule, as a validator applies it.** `IsAnchor` is not
relativised: which validator anchors a round is a schedule fact rather
than an observation, and that the block exists at all is implied by the
view holding a block that references it. -/
def CommittedIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  IsAnchor U r L ∧ SupportedIn U V L r ∧ LinkedIn U V L r

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable (CommittedIn U V L r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end BlackMarlin

end LeanDag
