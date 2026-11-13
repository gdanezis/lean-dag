import LeanDag.Scheme.AtomicBroadcast.Proof
/-!
# Validity under round-robin at Hybrid Mysticeti's committee

At `n = 3f + 2c + 1` the reliable set `T` has `n − f − c` members, so
`ValidityRoundRobin`'s premise `waveLength · (n − |T|) < n` fails once
`c ≥ 1`; `ValidityRoundRobinSilent`'s arithmetic premises hold for every
`f` and `c`, the crashed validators silent and `fb = f`.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

/-- At six validators, one Byzantine and one crashed, round-robin without
silence is out of reach. -/
example : ¬ (Params.hybridMysticeti 6 1 1).waveLength * (6 - 4) < 6 := by decide

/-- **Hybrid Mysticeti meets the silent premises** for every `f` and `c`
from `n = 3f + 2c + 1`, at `|T| = n − f − c` and `fb = f`. -/
example (n f c : ℕ) (h : 3 * f + 2 * c + 1 ≤ n) :
    (Params.hybridMysticeti n f c).commitThreshold ≤ n - f - c ∧
      (Params.hybridMysticeti n f c).skipThreshold ≤ n - f - c ∧
      (Params.hybridMysticeti n f c).voteOffset = 1 ∧
      ((Params.hybridMysticeti n f c).waveLength - 1) * f < n - f - c := by
  simp [Params.voteOffset, Params.hybridMysticeti]
  omega

/-- The atomic-broadcast claims, with validity under round-robin at silent
crashes among them. -/
example : AtomicBroadcast.ValidityRoundRobinSilent := AtomicBroadcast.validityRoundRobinSilent

end Scheme

end LeanDagTest
