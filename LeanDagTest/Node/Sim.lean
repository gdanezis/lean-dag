import LeanDagSim.Net
/-!
# Every row, simulated

One short simulation per row of the six partially synchronous rows,
each with a node down or a period before GST: the nodes still up build,
skip the slots of the node that is down, decide alike, and broadcast
only valid blocks. Each line reads: admissible, the round each honest
node reached, the slots it decided, those it skipped, whether the
decisions agree, whether the blocks are valid.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario's outcome, in one line. -/
def summary (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.admissible} {r.tops} {r.commits.map (·.length)} " ++
    s!"{r.commits.map fun l => (l.filter (·.2.isNone)).length} {r.agree} {r.valid}"

/-- info: "true [(some 41), (some 25), (some 41), (some 41)] [37, 23, 37, 37] [2, 0, 2, 2] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "cordial-miners", crash := [(1, 60)] }

/-- info: "true [(some 39), (some 38), (some 39), (some 38)] [37, 36, 37, 36] [2, 2, 2, 2] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", gst := 60, preMax := 25, seed := 2 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36), none] [35, 35, 35, 35, 35, 0] [5, 5, 5, 5, 5, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, crash := [(5, 0)] }

/--
info: "true [(some 40), (some 40), none, (some 40), (some 40), (some 40), (some 40), (some 40), (some 40)] [39, 39, 0, 39, 39, 39, 39, 39, 39] [5, 5, 0, 5, 5, 5, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "orcaella", n := 9, c := 1, crash := [(2, 0)] }

/-- info: "true [(some 18), (some 42), (some 42)] [17, 42, 42] [0, 7, 7] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "nemo-nemo", n := 3, f := 0, c := 1, crash := [(0, 40)] }

/--
info: "true [(some 36), (some 36), (some 36), (some 37), (some 36), (some 12)] [35, 35, 35, 36, 35, 10] [3, 3, 3, 4, 3, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "hybrid-mysticeti", n := 6, c := 1, crash := [(5, 30)] }

end Node

end LeanDagTest
