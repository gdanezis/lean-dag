import LeanDag.Barnacle.Progress.Statement
import LeanDag.Barnacle.MysticetiLive.Statement
import LeanDag.Barnacle.Odontoceti.Statement
import LeanDag.Barnacle.Nemo.Statement
/-!
# BN11 — the mechanism over a base protocol, end to end

BN8b gives runs of every height *given* the liveness clause, and BN10
proves that clause for round-robin at every count, for each of the
three rules; this file joins them. `RunsExist` is BN8b's consequent
discharged rather than assumed, and the three conjuncts instantiate it
at Mysticeti, Odontoceti and Nemo-Nemo under round-robin, at the gaps
BN10 establishes — `n + 2` for the three-round rule, `n + 1` for the
two-round ones — beyond which only each rule's committee bound is
asked.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Live

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Runs of every height, with no clause left over.** BN8b's
conclusion: on a DAG good from genesis, every height whose horizon fits
under `N` is reached — on any view caught up to `N`, which is what a
validator that has received everything up to the horizon holds. -/
def RunsExist (R : LiveRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R.toBaseRule) (c : ℕ) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N →
    R.toBaseRule.CoversUpto U V N → Rnd ≤ 1 →
    ∀ K, horizon P R c K ≤ N →
      Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V K)

/-- **BN11a** — Barnacle over Mysticeti, under round-robin, at gap
`n + 2`. -/
def MysticetiRuns : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)] (BlockId Payload : Type) [DecidableEq BlockId]
    (P : Params) (hk : Keyed (roundRobin n hn) P.maxLeaders)
    (upd : UpdateRule (mysticetiLive (Validator := Fin n) (BlockId := BlockId)
      (Payload := Payload)).toBaseRule),
    UpdBounded P upd →
    RunsExist (mysticetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload))
      P (roundRobin n hn) hk upd (n + 2)

/-- **BN11b** — Barnacle over Odontoceti, at gap `n + 1`. -/
def OdontocetiRuns : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults5 (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Params) (hk : Keyed (roundRobin n hn) P.maxLeaders)
    (upd : UpdateRule (odontocetiLive (Validator := Fin n) (BlockId := BlockId)
      (Payload := Payload)).toBaseRule),
    UpdBounded P upd →
    RunsExist (odontocetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload))
      P (roundRobin n hn) hk upd (n + 1)

/-- **BN11c** — Barnacle over Nemo-Nemo, at gap `n + 1`. The crash bound
is consumed nowhere: the slack is `n − majority`. -/
def NemoRuns : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [LeanDag.Nemo.CrashFaults (Fin n)] (BlockId Payload : Type)
    [DecidableEq BlockId] (P : Params) (hk : Keyed (roundRobin n hn) P.maxLeaders)
    (upd : UpdateRule (nemoLive (Validator := Fin n) (BlockId := BlockId)
      (Payload := Payload)).toBaseRule),
    UpdBounded P upd →
    RunsExist (nemoLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload))
      P (roundRobin n hn) hk upd (n + 1)

/-- The three protocols, end to end. -/
def Statement : Prop := MysticetiRuns ∧ OdontocetiRuns ∧ NemoRuns

end Live

end Barnacle

end LeanDag
