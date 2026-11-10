import LeanDag.Scheme.Model.AsyncPace
import LeanDag.Steelhead.Model.Coin
/-!
# The asynchronous rows: a coin per slot

`coinSlots S₀ h coin` is the schedule on the rounds and kinds of `S₀`
whose slot `s` is led by `coin s`. The rounds of `S₀` are strictly
increasing, one slot per round at most, so every leader map gives a schedule.
`AsyncPace.UndecidedBelow s₀` is the set of coin draws for `M` blocks of
`d` slots from slot `s₀` (`Steelhead.coinOfBlocksFrom`) under which some
slot below `s₀` is not decided on every reliable validator's own view from
some time on.

Definitions only; the claims are `Scheme/AsyncLive/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type}

/-- **The schedule a coin map elects**, on the rounds and kinds of `S₀`. -/
@[reducible] def coinSlots (S₀ : Slots Validator) (h : StrictMono S₀.slotRound) (coin : ℕ → Validator) :
    Slots Validator where
  slotRound := S₀.slotRound
  leader := coin
  mono := S₀.mono
  unbounded := S₀.unbounded
  keyed := fun _ _ hab => h.injective (congrArg Prod.fst hab)
  kind := S₀.kind

variable [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **The draws that leave a slot below `s₀` undecided** on some reliable
validator's own view at arbitrarily late times. -/
def AsyncPace.UndecidedBelow {q N : ℕ} {U : BlockRecord Validator BlockId Payload P honest}
    {T : Finset Validator} (ap : AsyncPace q U T N) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (S₀ : Slots Validator)
    (hS : StrictMono S₀.slotRound) (dflt : Validator) (s₀ M d : ℕ) :
    Set (Fin M → Fin d → Validator) :=
  {g | ¬ ap.Eventually fun V => ∀ s < s₀, ∃ v,
    (schemeAnchored p σ).Decided (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
      U V s v}

end Scheme

end LeanDag
