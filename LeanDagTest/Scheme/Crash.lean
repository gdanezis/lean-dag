import LeanDag.Scheme.Crash.Proof
import LeanDag.Scheme.Compose.Proof
import LeanDag.Scheme.Model.LeastSel
/-!
# Every validator crashes at once, on data

Hybrid Mysticeti at `f = 1`, `c = 1`, `n = 6`: every validator builds
round `0`, all six are down from time `1` to `10`, and on restart each
rebuilds every round it missed. The run is a crash run of the row
(`Full.crashRun`), and read past `max gst tr = 11` it is a responsive run
(`CrashRun.toReactive`), so the row's liveness applies from round `11`.
-/

namespace LeanDagTest

namespace Crash

open LeanDag LeanDag.Scheme

attribute [local instance] noFaults

@[reducible] def hmSlots : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 6, Nat.mod_lt _ (by omega)⟩)

attribute [local instance 3000] hmSlots

abbrev hmP : Params := Params.hybridMysticeti 6 1 1

abbrev hmσ : VoteSel (Fin 6) (Lex (ℕ × Fin 6)) Unit
    (ValidAt 4 (Clause.distinct.and Clause.selfParent)) Finset.univ := leastSel

theorem hm_row : hmP.PSRow 6 1 1 := Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))

/-- **All six validators down from `1` to `10`.** -/
def allDown (N : ℕ) : CrashRun 4 hmP hmσ (Full.record (n := 6) (q := 4) (by omega) N)
    Finset.univ N :=
  Full.crashRun 4 hmP (Responsive.psRow_cert_le hm_row) hmσ 10

example (N : ℕ) : ∀ v t, 1 ≤ t → t ≤ 10 → ¬ (allDown N).up v t := by
  intro v t h1 h2 h
  rcases h with h | h <;> omega

/-- **Read as a responsive run, its GST is the restart.** -/
example (N : ℕ) : (allDown N).toReactive.gst = 11 := rfl

end Crash

end LeanDagTest

#print axioms LeanDag.Scheme.Crash.holds
#print axioms LeanDag.Scheme.Compose.holds
