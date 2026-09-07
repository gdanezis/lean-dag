import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Mysticeti.Statement
/-!
# Barnacle over Mysticeti — liveness

Mysticeti as a live rule, its descent laws, and the paper's A4 for
Mysticeti under its own schedule: round-robin is live at every leader
count (`barnacle.md` §8, F3). A good DAG is `Timed.Good` at the core's
fault model — a correct quorum synchronised from `Rnd` and populating
every round to `N` (report §5). The slack is `f`, and the committee
bound the pigeonhole needs, `3f + 1 ≤ n`, is `Faults.card_validators`.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Mysticeti as a live rule**, at the core's fault model. -/
def mysticetiLive [Faults Validator] : LiveRule Validator BlockId Payload :=
  liveOfAnchored (coreAnchored Validator BlockId Payload) (coreReliability Validator)

namespace MysticetiLive

/-- **Mysticeti has the descent laws at slack `f`.** -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [DecidableEq BlockId],
    (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **Mysticeti under round-robin is live at every count** — the paper's
A4 for its own schedule, with gap `n + 2`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)] (BlockId Payload : Type) [DecidableEq BlockId]
    (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (mysticetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 2)

/-- The descent laws, and liveness under round-robin at every count. -/
def Statement : Prop := Descent ∧ RoundRobinLive

end MysticetiLive

end Barnacle

end LeanDag
