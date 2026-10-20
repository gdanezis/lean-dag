import LeanDagSim.Net
/-!
# Every row, simulated

One short simulation per row of the six partially synchronous rows,
each with a node down or a period before GST, two with an equivocator,
one with a node withholding a block it leads from one node until
that node has asked for it, and three with a node that restarts after a
downtime: the honest nodes build, skip the slots of a node that is down,
fetch what they did not receive, asking again on account of each block
that needs it, decide alike, and make only valid blocks above round `0`.
A restarting node asks its peers for their bases; one whose peers have
pruned past its top bootstraps, and one whose store holds a quorum at a
round above its top skips there. Each line reads: admissible, the round
each honest node reached, the slots it decided, those it skipped,
whether two nodes that decide a slot decide it alike, whether the blocks
are valid, and, for the restarts, whether any two nodes' decisions are
prefix-comparable, and the skips and the bootstraps made.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario's outcome, in one line. -/
def summary (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.admissible} {r.tops} {r.commits.map (·.length)} " ++
    s!"{r.commits.map fun l => (l.filter (·.2.isNone)).length} {r.agree} {r.valid}"

/-- A scenario's outcome, with whether the decisions are prefix-comparable,
and the skips and the bootstraps made. -/
def summaryR (sc : Scenario) : String :=
  let r := simulate sc
  s!"{summary sc} {r.prefixes} {r.skips} {r.boots}"

/--
info: "true [(some 41), (some 25), (some 41), (some 41)] [37, 23, 37, 37] [2, 0, 2, 2] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "cordial-miners", crash := [(1, 60)] }

/--
info: "true [(some 41), (some 40), (some 41), (some 41)] [39, 39, 39, 39] [1, 1, 1, 1] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", gst := 60, preMax := 25, seed := 2 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36), none] [35, 35, 35, 35, 35, 0] [5, 5, 5, 5, 5, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, crash := [(5, 0)] }

/--
info: "true [(some 41), (some 40), none, (some 41), (some 41), (some 41), (some 41), (some 41), (some 40)] [40, 40, 0, 40, 40, 40, 40, 40, 39] [5, 5, 0, 5, 5, 5, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "orcaella", n := 9, c := 1, crash := [(2, 0)] }

/-- info: "true [(some 21), (some 45), (some 45)] [20, 42, 42] [0, 6, 6] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "nemo-nemo", n := 3, f := 0, c := 1, crash := [(0, 40)] }

/--
info: "true [(some 37), (some 37), (some 36), (some 36), (some 36), (some 11)] [36, 36, 36, 36, 36, 9] [4, 4, 4, 4, 4, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "hybrid-mysticeti", n := 6, c := 1, crash := [(5, 30)] }

/-- info: "true [(some 24), (some 23), (some 23)] [22, 22, 22] [6, 6, 6] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", byz := [3], byzUntil := 150 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36)] [35, 35, 35, 35, 35] [5, 5, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, byz := [0], byzUntil := 150 }

/--
info: "true [(some 141), (some 141), (some 141), (some 141)] [139, 139, 139, 139] [0, 0, 0, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", withhold := some (3, 2, 7), delayMax := 1 }

/--
info: "true [(some 58), (some 58), (some 58), (some 58)] [56, 56, 56, 56] [1, 1, 1, 1] true true true 1 0"
-/
#guard_msgs in
#eval summaryR { horizon := 150, row := "mysticeti", recover := [(1, 40, 46)], lag := 6 }

/--
info: "true [(some 56), (some 56), (some 56), (some 56)] [54, 54, 54, 54] [1, 1, 1, 1] true true true 1 0"
-/
#guard_msgs in
#eval summaryR { horizon := 150, row := "mysticeti", recover := [(1, 40, 60)], lag := 6 }

/--
info: "true [(some 63), (some 63), (some 63), (some 63)] [61, 61, 61, 61] [0, 0, 0, 0] true true true 0 0"
-/
#guard_msgs in
#eval summaryR { horizon := 150, row := "mysticeti", recover := [(1, 40, 46)] }

/--
info: "true [(some 49), (some 49), (some 49), (some 49)] [47, 47, 47, 47] [2, 2, 2, 2] true true true 1 1"
-/
#guard_msgs in
#eval summaryR { horizon := 150, row := "mysticeti", recover := [(1, 40, 90)] }

end Node

end LeanDagTest
