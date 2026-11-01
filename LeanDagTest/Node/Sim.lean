import LeanDagSim.Net
/-!
# Every row, simulated

One short simulation per row of the six partially synchronous rows, each
with a node down or a period before GST, two with an equivocator, and
one with a node withholding a block it leads from one node until that
node has asked for it: the honest nodes build, skip the slots of a node
that is down, sync what they did not receive from the peer that
announced it, decide alike, and make only valid blocks above round `0`.
Each line reads: admissible, the round each honest node reached, the
slots it decided, those it skipped, whether two nodes that decide a slot
decide it alike, and whether the blocks are valid.
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
info: "true [(some 38), (some 26), (some 38), (some 38)] [37, 24, 37, 37] [2, 0, 2, 2] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "cordial-miners", crash := [(1, 60)] }

/--
info: "true [(some 42), (some 42), (some 42), (some 42)] [41, 40, 40, 40] [0, 0, 0, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", gst := 60, preMax := 25, seed := 2 }

/--
info: "true [(some 33), (some 33), (some 33), (some 33), (some 33), none] [32, 32, 32, 32, 32, 0] [5, 5, 5, 5, 5, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "blue-bottle", n := 6, crash := [(5, 0)] }

/--
info: "true [(some 38), (some 38), none, (some 38), (some 38), (some 38), (some 38), (some 38), (some 38)] [37, 38, 0, 37, 37, 37, 37, 37, 37] [4, 4, 0, 4, 4, 4, 4, 4, 4] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "orcaella", n := 9, c := 1, crash := [(2, 0)] }

/-- info: "true [(some 19), (some 39), (some 39)] [18, 39, 39] [0, 6, 6] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "nemo-nemo", n := 3, f := 0, c := 1, crash := [(0, 40)] }

/--
info: "true [(some 35), (some 35), (some 35), (some 35), (some 35), (some 12)] [34, 34, 34, 34, 34, 11] [3, 3, 3, 3, 3, 0] true true"
-/
#guard_msgs in
#eval summary { horizon := 150, row := "hybrid-mysticeti", n := 6, c := 1, crash := [(5, 30)] }

/-- info: "true [(some 53), (some 53), (some 53)] [52, 52, 52] [13, 13, 13] true true" -/
#guard_msgs in
#eval summary { horizon := 150, row := "mysticeti", byz := [3], byzUntil := 150 }

/--
info: "true [(some 47), (some 47), (some 47), (some 47), (some 47)] [46, 46, 46, 46, 46] [7, 7, 7, 7, 7] true true"
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
holds a sync it asked for before the crash, whose answer was lost; it
asks again on restart. -/

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
info: "true [(some 24), (some 24), (some 24), none] [24, 24, 24, 0] [6, 6, 6, 0] true true (5, 157, 161)"
-/
#guard_msgs in
#eval outageLine
  { horizon := 300
    row := "mysticeti"
    crash := [(3, 0)]
    outages := [(2, 30, 150)] }

/-- info: "true [(some 41), (some 41), none] [41, 41, 0] [13, 13, 0] true true (16, 266, 266)" -/
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
info: "true [(some 100), (some 100), (some 100), (some 100), (some 100), (some 100)] [98, 98, 99, 98, 98, 98] [0, 0, 0, 0, 0, 0] true true (17, 109, 103) (17, 109, 103) (17, 108, 103) (17, 109, 103) (17, 107, 103) (17, 106, 103)"
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
