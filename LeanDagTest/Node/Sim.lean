import LeanDagSim.Net
/-!
# Every row, simulated

One short simulation per row of the six partially synchronous rows,
each with a node down or a period before GST, two with an equivocator,
and one with a node withholding a block it leads from one node until
that node has asked for it: the honest nodes build, skip the slots of a
node that is down, fetch what they did not receive, asking again on
account of each block that needs it, decide alike, and make only valid
blocks above round `0`. Each line reads: admissible, the round each
honest node reached, the slots it decided, those it skipped, whether two
nodes that decide a slot decide it alike, and whether the blocks are
valid.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario's outcome, in one line. -/
def summary (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.admissible} {r.tops} {r.commits.map (·.length)} " ++
    s!"{r.commits.map fun l => (l.filter (·.2.isNone)).length} {r.agree} {r.valid}"

/--
info: "true [(some 38), (some 24), (some 38), (some 38)] [33, 22, 37, 33] [2, 0, 3, 2] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "cordial-miners", crash := [(1, 60)] }

/--
info: "true [(some 42), (some 42), (some 42), (some 43)] [40, 40, 40, 41] [1, 1, 1, 1] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", gst := 60, preMax := 25, seed := 2 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36), none] [35, 35, 35, 35, 35, 0] [5, 5, 5, 5, 5, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, crash := [(5, 0)] }

/--
info: "true [(some 40), (some 39), none, (some 40), (some 40), (some 39), (some 40), (some 40), (some 40)] [39, 38, 0, 39, 39, 38, 39, 39, 39] [5, 4, 0, 5, 5, 4, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "orcaella", n := 9, c := 1, crash := [(2, 0)] }

/-- info: "true [(some 19), (some 42), (some 42)] [18, 42, 42] [0, 7, 7] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "nemo-nemo", n := 3, f := 0, c := 1, crash := [(0, 40)] }

/--
info: "true [(some 38), (some 38), (some 38), (some 37), (some 38), (some 12)] [36, 36, 36, 36, 36, 10] [4, 4, 4, 4, 4, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "hybrid-mysticeti", n := 6, c := 1, crash := [(5, 30)] }

/-- info: "true [(some 23), (some 24), (some 23)] [22, 22, 22] [6, 6, 6] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", byz := [3], byzUntil := 150 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36)] [36, 35, 35, 35, 35] [5, 5, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, byz := [0], byzUntil := 150 }

/--
info: "true [(some 141), (some 141), (some 141), (some 141)] [139, 139, 139, 139] [0, 0, 0, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", withhold := some (3, 2, 7), delayMax := 1 }

end Node

end LeanDagTest
