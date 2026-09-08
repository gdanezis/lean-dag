import LeanDag.FinWhale.Procedure.Pass
import LeanDag.FinWhale.Model.Liveness
import LeanDag.Mysticeti.ViewPace
import LeanDag.FinWhale.Holdings
import LeanDag.FinWhale.Procedure.View
/-!
# FinWhale — the pass over a validator's holdings

Procedure side: these mention a verdict assignment or the reverse pass.
-/

namespace LeanDag
namespace FinWhale
variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D : Dag Validator BlockId Payload} {S : Slots Validator}
variable {Elig : ℕ → ℕ → Prop} [DecidableRel Elig]
variable {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {M : ℕ}
variable [LinearOrder BlockId]

/-- **Every slot below the horizon is decided**, by a validator whose
view is its own holdings and whose verdicts are the reverse pass. Nothing
about the validator itself is a hypothesis; what remains is about the
schedule and the DAG reaching the rounds. -/
theorem all_decided_of_pass (pc : PaceCore U (Correct : Finset Validator) M)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hle : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pc.top u, n ≤ pc.built u n)
    {R : ℕ} (hgst : pc.gst ≤ R) {v : Validator} (hv : v ∈ (Correct : Finset Validator))
    {choose : BlockId → ℕ → Option BlockId} {Np N r : ℕ}
    (hhorizon : ∀ b ∈ pc.holds v (settled pc), (D.block b).round ≤ Np)
    (hcommits : CommitsCorrectLeaders S D R N) (hrr : RoundRobin S.leader)
    (hEl : ∀ r a, Elig r a ↔ r + 2 < a) (hid : ∀ k, S.slotRound k = k) (hNM : N ≤ M)
    (hN : max r R + (3 * F.f + 5) ≤ N) :
    decOf S Elig (holdsView pc hids hblk hv (settled pc)).toRecord
      choose Np r ≠ Verdict.undecided := by
  have hlt : ∀ r a, Elig r a → r < a := fun r a h => by have := (hEl r a).1 h; omega
  have hrle : ∀ r, S.slotRound r ≤ Np → r ≤ Np := fun r h => by rwa [hid] at h
  exact all_decided_of_view (V := holdsView pc hids hblk hv (settled pc))
    (wellFormed_decOf hhorizon hlt hrle choose)
    (fun n hRn hnN b hb hbc =>
      held_of_pace pc hids hblk hle card_correct hgst hv n hRn (by omega) b hb hbc)
    hcommits hrr hEl hid hN

end FinWhale

end LeanDag
