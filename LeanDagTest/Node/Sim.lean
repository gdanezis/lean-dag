import LeanDagSim.Net
/-!
# Every row, simulated

One short simulation per row of the six partially synchronous rows,
each with a node down or a period before GST, two with an equivocator,
one with a node withholding a block it leads from one node until
that node has asked for it, and three with a node that restarts after a
downtime: the honest nodes build, skip the slots of a node that is down,
fetch what they did not receive, asking again on account of each block
that needs it, decide alike, and make only valid blocks. A restarting
node that fetches the line of a block two rounds or more above its own
jumps there with one message: with a horizon lag of `6` it does, after
six ticks down and after twenty; with the lag of `2` it stays at its
last round, since it fetches one round below per request while the
peers' horizon rises a round per round (bootstrap is for this). Each
line reads: admissible, the round each honest node reached, the slots
it decided, those it skipped, whether the decisions agree, whether the
blocks are valid, and, for the restarts, the jump messages sent.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario's outcome, in one line. -/
def summary (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.admissible} {r.tops} {r.commits.map (·.length)} " ++
    s!"{r.commits.map fun l => (l.filter (·.2.isNone)).length} {r.agree} {r.valid}"

/-- A scenario's outcome, with the jump messages sent. -/
def summaryJ (sc : Scenario) : String :=
  s!"{summary sc} {(simulate sc).jumps}"

/--
info: "true [(some 41), (some 26), (some 41), (some 41)] [37, 24, 37, 37] [2, 0, 2, 2] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "cordial-miners", crash := [(1, 60)] }

/--
info: "true [(some 42), (some 41), (some 41), (some 41)] [40, 39, 39, 39] [2, 2, 2, 2] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", gst := 60, preMax := 25, seed := 2 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36), none] [35, 35, 35, 35, 35, 0] [5, 5, 5, 5, 5, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, crash := [(5, 0)] }

/--
info: "true [(some 39), (some 39), none, (some 39), (some 39), (some 39), (some 39), (some 39), (some 39)] [38, 38, 0, 38, 38, 38, 38, 38, 38] [4, 4, 0, 4, 4, 4, 4, 4, 4] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "orcaella", n := 9, c := 1, crash := [(2, 0)] }

/-- info: "true [(some 18), (some 42), (some 42)] [17, 42, 42] [0, 7, 7] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "nemo-nemo", n := 3, f := 0, c := 1, crash := [(0, 40)] }

/--
info: "true [(some 36), (some 36), (some 37), (some 36), (some 37), (some 12)] [35, 35, 36, 35, 36, 10] [3, 3, 4, 3, 4, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "hybrid-mysticeti", n := 6, c := 1, crash := [(5, 30)] }

/-- info: "true [(some 24), (some 24), (some 24)] [23, 23, 22] [5, 5, 5] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", byz := [3], byzUntil := 150 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36)] [36, 36, 36, 36, 36] [5, 5, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, byz := [0], byzUntil := 150 }

/--
info: "true [(some 141), (some 141), (some 141), (some 141)] [139, 139, 139, 139] [0, 0, 0, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", withhold := some (3, 2, 7), delayMax := 1 }

/--
info: "true [(some 63), (some 64), (some 63), (some 64)] [62, 62, 62, 62] [0, 0, 0, 0] true true 1"
-/
#guard_msgs in
#eval summaryJ { horizon := 150, row := "mysticeti", recover := [(1, 40, 46)], lag := 6 }

/--
info: "true [(some 58), (some 58), (some 58), (some 58)] [56, 56, 56, 56] [1, 1, 1, 1] true true 1"
-/
#guard_msgs in
#eval summaryJ { horizon := 150, row := "mysticeti", recover := [(1, 40, 60)], lag := 6 }

/--
info: "true [(some 37), (some 18), (some 37), (some 37)] [36, 16, 35, 35] [4, 0, 4, 4] true true 0"
-/
#guard_msgs in
#eval summaryJ { horizon := 150, row := "mysticeti", recover := [(1, 40, 46)] }

end Node

end LeanDagTest
