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
info: "true [(some 40), (some 40), (some 41), (some 40)] [38, 39, 39, 38] [0, 0, 0, 0] true true"
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

/-- info: "true [(some 23), (some 23), (some 23)] [22, 22, 22] [6, 6, 6] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", byz := [3], byzUntil := 150 }

/--
info: "true [(some 36), (some 36), (some 36), (some 36), (some 36)] [36, 35, 36, 35, 35] [5, 5, 5, 5, 5] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, byz := [0], byzUntil := 150 }

/--
info: "true [(some 141), (some 141), (some 141), (some 141)] [139, 139, 139, 139] [0, 0, 0, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", withhold := some (3, 2, 7), delayMax := 1 }

/-! ## Outages

A node down for a while loses what is sent to it, and restarts from its
state. Each line adds, for each outage, the highest round an honest node
built by the restart, when the restarted node built above it, and when
an honest node next decided. With `f` nodes silent, an outage of one more
stalls the others until it restarts. At Nemo-Nemo the restarted node
holds a block pending whose history it asked for before the crash, and
the answer was lost; resending asks for it again. -/

/-- A scenario's outcome, with each outage's recovery: the top round at
the restart, when the restarted node built above it, and when an honest
node next decided. -/
def outageLine (sc : Scenario) : String :=
  let r := simulate sc
  let fmt (t : Option ℕ) := (t.map toString).getD "none"
  summary sc ++ String.join (sc.outages.map fun (v, _, b) =>
    let (R, t₁, t₂) := recovery r v b
    s!" ({R}, {fmt t₁}, {fmt t₂})")

/--
info: "true [(some 28), (some 28), (some 28), none] [28, 28, 28, 0] [7, 7, 7, 0] true true (6, 155, 155)"
-/
#guard_msgs in
#eval outageLine
  { horizon := 300
    row := "mysticeti"
    crash := [(3, 0)]
    outages := [(2, 30, 150)] }

/-- info: "true [(some 44), (some 45), none] [44, 44, 0] [14, 14, 0] true true (18, 270, 265)" -/
#guard_msgs in
#eval outageLine
  { horizon := 400
    row := "nemo-nemo"
    n := 3
    f := 0
    c := 1
    gst := 100
    preMax := 25
    crash := [(2, 0)]
    outages := [(0, 150, 260)] }

/--
info: "true [(some 100), (some 100), (some 101), (some 100), (some 101), (some 101)] [98, 99, 99, 98, 99, 99] [0, 0, 0, 0, 0, 0] true true (17, 106, 103) (17, 107, 103) (17, 107, 103) (17, 108, 103) (17, 109, 103) (17, 104, 103)"
-/
#guard_msgs in
#eval outageLine
  { horizon := 300
    row := "hybrid-mysticeti"
    n := 6
    c := 1
    outages := (List.range 6).map fun v => (v, 40, 100) }

end Node

end LeanDagTest
