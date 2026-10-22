import LeanDagSim.Net
/-!
# Attacks, simulated

`docs/validator.md` §6, step 7.4. At the Mysticeti row with `n = 4` and
`f = 1`, node `3` runs the honest program and mounts one attack. Each
line reads: the round each honest node reached, the slots it decided,
whether two nodes that decide a slot decide it alike, whether any two
nodes' decisions are prefix-comparable, whether the honest blocks are
valid, and the inputs the signature checks dropped.

With the network checking signatures, which is what the claims over
traces assume of authentication, every attack leaves agreement,
prefix-comparability and validity intact. Without the checks, blocks
forged in node `0`'s name are accepted by its peers as node `0`'s, and
their later blocks reference them; node `0` drops every block in its own
name, so it never holds their histories and stays at round `2`, while
agreement, prefix-comparability and validity still hold. The liveness
claim assumes authenticated blocks (`Converge.TimelyAuthentic`), which
excludes this run.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario under attack: node `3` attacks. -/
def attackedBy (as : List Attack) (verify : Bool := true) : Scenario :=
  { horizon := 150, row := "mysticeti", adv := [3], attacks := as, verify := verify }

/-- A scenario's outcome under attack, in one line. -/
def attackLine (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.tops} {r.commits.map (·.length)} {r.agree} {r.prefixes} {r.valid} {r.dropped}"

/-- info: "[(some 63), (some 63), (some 63)] [61, 61, 62] true true true 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks])

/-- info: "[(some 64), (some 64), (some 64)] [62, 62, 62] true true true 192" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor])

/-- info: "[(some 23), (some 23), (some 23)] [22, 22, 22] true true true 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.twinSplit])

/-- info: "[(some 24), (some 24), (some 24)] [24, 24, 24] true true true 6" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks, .forgedAuthor, .twinSplit])

/-! ## Without the signature checks -/

/-- info: "[(some 2), (some 35), (some 35)] [0, 33, 33] true true true 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor] (verify := false))

end Node

end LeanDagTest
