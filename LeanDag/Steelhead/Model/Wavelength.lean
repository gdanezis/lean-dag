import Mathlib.Data.Nat.Basic
/-!
# Steelhead — the wavelength function

Steelhead composes two commit rules over one DAG by giving every slot a
**kind**, the mode it is decided in, and letting the kind say how many
rounds that slot reads: `ws` for a synchronous slot and `wa` for an
asynchronous one (`steelhead.md` §1). The kind is the schedule's, beside
the slot's round and its leader (`Slots.kind`, `docs/kinds.md`), so the
mode is an interpretation of the DAG and touches no block. Which slots
are asynchronous is then a property of the schedule: the period `p`
makes every `p`-th round one.

**The mode is the wavelength alone.** The two modes also elect their
leaders differently, and that difference is not in the rule: the
relation reads the schedule's leader at every slot whatever the slot's
wavelength, and a claim that needs the coin's leader at an asynchronous
round takes it as a hypothesis (`Safety/Statement.lean`, SH5b).
Agreement therefore holds at every schedule.

**Definitions only.** The rule that consumes a wavelength function is in
`Decision.lean`; the results about it are stated in
`<Result>/Statement.lean` files and proved in their `Proof.lean`.

The two ends of the dial are schedules, not wavelength functions: `p = 1`
gives every slot kind `1` and so the wave `wa` everywhere, and a schedule
that assigns no kinds at all leaves every slot at `Slots.kind`'s default
`0` and so at `ws`. Both are Mahi-Mahi's rule at one wave, the second
Mysticeti's when `ws = 3` (`Safety/Statement.lean`, SH4).
-/

namespace LeanDag

namespace Steelhead

/-- **The wavelength of a kind**: `ws` at a synchronous slot, kind `0`,
and `wa` at an asynchronous one. Kind `0` is what `Slots.kind` assigns
when a schedule says nothing, so a schedule with no kinds reads `ws`
everywhere, and no kind above `1` arises from the pair. -/
def wavelength (ws wa : ℕ) : ℕ → ℕ := fun κ => if κ = 0 then ws else wa

/-- **The periodic assignment of kinds**: asynchronous, kind `1`, at
every `p`-th round, synchronous at the others. A schedule takes it as its
`kind` field, `kind k = periodicKind p (slotRound k)`. At `p = 0` Lean's
`r % 0 = r` makes only round `0` asynchronous. No result excludes that
period and none needs to: the claims take the wavelength function and the
schedule themselves, and one that needs a bound on `p` states it. -/
def periodicKind (p : ℕ) : ℕ → ℕ := fun r => if r % p = 0 then 1 else 0

/-- **The periodic wavelength**: `wa` at every `p`-th round, `ws` at the
others. The paper's `w(r) = wa if r mod p = 0 else ws`, kept as the
formula the arc is measured against; the rule itself reads
`wavelength ws wa` at the slot's kind. -/
def periodic (ws wa p : ℕ) : ℕ → ℕ := fun r => if r % p = 0 then wa else ws

/-- A round is **asynchronous** under the period `p` when it is a multiple
of `p`: its slot is decided by the asynchronous rule with a coin-elected
leader. -/
def IsAsync (p r : ℕ) : Prop := r % p = 0

instance (p r : ℕ) : Decidable (IsAsync p r) := inferInstanceAs (Decidable (_ = _))

end Steelhead

end LeanDag
