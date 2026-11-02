import LeanDag.Scheme.Model.TryDecide
/-!
# The witness of a decision

`docs/node-sync.md` D13: the blocks that decide a slot, which a node keeps
below its cut as the slot's proof.

* `anchorWitness`: along the walk over the later slots, the witnesses of the
  skipped eligible slots it passes and of the anchor it stops at.
* `witnessAt N k`: the witness of slot `k`'s decision, scanning to slot `N`:
  the held blames of a direct skip, the held certificates of a direct commit,
  and for an indirect verdict the witness of its walk.

The proof of D13 is the witness with its histories down to the round below
the slot. Definitions only; the claims are `Scheme/Helpers/Witness.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
variable (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)

/-- The witness of the walk over the later slots, given the witness `wit j`
of each slot `j`. -/
def anchorWitness (k : ℕ) (wit : ℕ → Finset BlockId) :
    List (ℕ × Option (Option BlockId)) → Finset BlockId
  | [] => ∅
  | (j, s) :: rest =>
    if S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound j then
      match s with
      | none => ∅
      | some none => wit j ∪ anchorWitness k wit rest
      | some (some _) => wit j
    else anchorWitness k wit rest

/-- **The witness of slot `k`'s decision**, scanning to slot `N`. -/
def witnessAt (N k : ℕ) : Finset BlockId :=
  match tryDirect p σ U V k with
  | some none => blamersAt p σ U k ∩ V.ids
  | some (some L) => certsAt p σ U L (S.slotRound k) ∩ V.ids
  | none => anchorWitness (S := S) p k (fun j => if _ : k < j ∧ j ≤ N then witnessAt N j else ∅)
      (scan p σ U V N (N - k))
termination_by N + 1 - k

end Scheme

end LeanDag
