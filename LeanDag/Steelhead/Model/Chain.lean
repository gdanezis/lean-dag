import LeanDag.Steelhead.Model.Decision
/-!
# Steelhead — the chain verdict

A committed asynchronous slot does not decide the synchronous slots
below it: the anchor search of Algorithm 1 stops at an undecided slot,
and under asynchrony an adversary who knows the leader keeps every
synchronous slot undecided at no cost (`steelhead.md` §4, the witness is
`LeanDagTest/Steelhead/Stall.lean`). So the interval's anchor, the
agreed event the period update reads, cannot come from the output. It
comes from the **chain verdict**: the asynchronous rule read on *every*
round with that round's coin leader, anchored on chain commits only, so
that no known-leader slot lies on the chain and nothing the adversary
can hold undecided blocks it. Chain verdicts are never sequenced or
output; they drive the period update (`Period.lean`).

**The chain is the Mahi-Mahi arc at the identity schedule.** One slot
per round, the round's coin leader as the slot's leader, wave `wa`: the
chain relation is Mahi-Mahi's `Decided wa` at `Slots.identity coin`,
nothing new. Its agreement is MM1c; its liveness is MM3 with the
unpredictable-leader clause at that schedule. Reading the chain at every
round rather than at the asynchronous slots alone is what keeps it
independent of the period: which rounds are asynchronous above the
interval under scan is not yet known, and a chain that read only those
would wait on a period its own verdicts are meant to fix. This is the
reference implementation's reading (`committer.rs`, `compute_chain`).

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The chain schedule**: one slot per round, led by `coin r`, the
coin-elected leader of round `r`. The coin is modelled by its effect, as
in the Mahi-Mahi arc: `coin` is any map, and the unpredictability clause
of the liveness statements is what a coin revealed after the votes makes
true. -/
abbrev chainSlots (coin : ℕ → Validator) : Slots Validator := Slots.identity coin

/-- **The chain verdict** at wave `wa` under the coin `coin`: Mahi-Mahi's
relation at the chain schedule. `ChainDecided wa coin U V r v` is the
chain verdict `v` of round `r`, read from the view `V`. -/
abbrev ChainDecided (wa : ℕ) (coin : ℕ → Validator)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  MahiMahi.Decided (S := chainSlots coin) wa U V

end Steelhead

end LeanDag
