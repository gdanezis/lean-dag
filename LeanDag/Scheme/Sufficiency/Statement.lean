import LeanDag.Scheme.Model.Rule
import LeanDag.Properties.Agree
import LeanDag.Common.Anchored.Band
/-!
# The table's inequalities suffice for agreement — statement

`docs/scheme.md` §7. A record is read with three numbers: `n` validators,
blocks that reference `q` distinct authors one round down, and at most
`f` validators outside the record's honest set, the validators that never
equivocate. A crash-prone validator is honest in this sense; crash faults
enter only through `q`. At every vote-selection rule, every row that
tolerates the record's faults (`Params.Tolerates`: the inequalities cover
it, `Params.Covered`) decides alike from two views (`CoveredAgree`):

* a row whose vote is its certificate and whose wave is at least two,
  meeting `Params.TwoRound n f q`;
* a row that certifies votes one round later, with a wave of at least
  three and a link of one certificate, meeting `Params.ThreeRound n f q`;
* where nobody equivocates (`f = 0`), the same rows meeting the weaker
  `Params.TwoRoundCrash n q` or `Params.ThreeRoundCrash n q`, without the
  inequality against an equivocating twin or the one making certificates
  unique.

Every row of the table is covered (`Scheme.Table.RowsCovered`), so every
row agrees.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Sufficiency

open LeanDag.Properties

/-- **Every row the inequalities cover decides alike from two views.** -/
def CoveredAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest),
    p.Tolerates honest f q → Agree (schemeAnchored p σ).toDagRule

/-- The inequalities suffice. -/
def Statement : Prop := CoveredAgree

end Sufficiency

end Scheme

end LeanDag
