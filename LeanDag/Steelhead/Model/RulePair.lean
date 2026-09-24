import LeanDag.Steelhead.Model.Compose
import LeanDag.Steelhead.Model.Wavelength
/-!
# Steelhead — a pair of rules

The paper states Theorem 3 for two rules of an interface, a synchronous
rule `R_s` with a known leader and an asynchronous rule `R_a` with a hidden
one, composed by the kind of the slot. `RulePair` is that pair as data: two
anchored rules on one committee that agree on the rung count, the
tie-break and the anchor, the data the anchored relation reads without a
slot, so that
a composite of the two runs one anchor search. `rules` assigns the
synchronous rule to kind `0`, what `Slots.kind` assigns when a schedule says
nothing, and the asynchronous rule to every other kind, as `wavelength ws wa`
assigns the waves; `steelheadAt` is the composite (`Compose.lean`) of that
assignment. Which slots are asynchronous is the schedule's business:
`periodicKind p` for the paper's dial, `adaptiveKind I per` for a derived
period sequence. The asynchronous rule on its own reads the control and chain
verdicts (`Chain.lean`), which is why the pair keeps the two rules apart
rather than only their composite.

The two pairs the paper instantiates are `mmPair` and `bbPair`
(`Pair.lean`).

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **A pair of rules**: the synchronous and the asynchronous rule of the interface, agreeing on
the rung count, the tie-break and the anchor. -/
structure RulePair (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] where
  /-- The synchronous rule, `R_s`. -/
  sync : AnchoredRule Validator BlockId Payload ValidWrt Correct
  /-- The asynchronous rule, `R_a`. -/
  async : AnchoredRule Validator BlockId Payload ValidWrt Correct
  /-- Both read the same number of rungs. -/
  rungs_eq : async.rungs = sync.rungs
  /-- Both break ties the same way. -/
  tie_eq : async.tie = sync.tie
  /-- Both know the same of a committed anchor. -/
  anchor_eq : async.Anchor = sync.Anchor

namespace RulePair

/-- **The rule of each kind**: the synchronous rule at kind `0`, the asynchronous rule at every
other kind, as `wavelength ws wa` reads the waves. -/
def rules (p : RulePair Validator BlockId Payload) :
    ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  fun κ => if κ = 0 then p.sync else p.async

end RulePair

/-- **Steelhead at a pair**: the composite of the pair's rules, a slot decided by the rule of its
kind. -/
def steelheadAt (p : RulePair Validator BlockId Payload) :
    AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  compose p.rules

end Steelhead

end LeanDag
