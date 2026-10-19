import LeanDagSim.Net
/-!
# Attacks, simulated

`docs/validator.md` §6, step 7.4. At the Mysticeti row with `n = 4` and
`f = 1`, node `3` runs the honest program and mounts one attack, while
node `1` is down from tick `40` to tick `90` and rejoins by bootstrap,
from the bases and certificates its peers serve. Each line reads: the
round each honest node reached, the slots it decided, whether two nodes
that decide a slot decide it alike, whether any two nodes' decisions are
prefix-comparable, whether the honest blocks are valid, the bootstraps
made, and the inputs the signature checks dropped.

With the network checking signatures, which is what the claims over
traces assume of authentication, every attack leaves agreement,
prefix-comparability and validity intact. Without the checks, a
certificate of fabricated decisions can be adopted, and the joiner's
decisions then disagree with its peers'; and blocks forged in an honest
node's name halt that node, since it drops blocks claiming its identity
and so never completes the histories that reference them.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario under attack: node `3` attacks, node `1` rejoins. -/
def attackedBy (as : List Attack) (verify : Bool := true) (seed : ℕ := 1) : Scenario :=
  { horizon := 150, row := "mysticeti", adv := [3], attacks := as, verify := verify,
    recover := [(1, 40, 90)], seed := seed }

/-- A scenario's outcome under attack, in one line. -/
def attackLine (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.tops} {r.commits.map (·.length)} {r.agree} {r.prefixes} {r.valid} {r.boots} {r.dropped}"

/-- info: "[(some 48), (some 48), (some 47)] [46, 46, 45] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase])

/-- info: "[(some 48), (some 48), (some 47)] [46, 46, 45] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.splitBase])

/-- info: "[(some 48), (some 48), (some 47)] [46, 46, 45] true true true 1 2" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert])

/-- info: "[(some 52), (some 51), (some 52)] [50, 49, 50] true true true 1 2" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert] (seed := 3))

/-- info: "[(some 49), (some 50), (some 49)] [47, 48, 47] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.conflictProposals])

/-- info: "[(some 43), (some 44), (some 44)] [42, 42, 42] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks])

/-- info: "[(some 49), (some 49), (some 49)] [47, 47, 47] true true true 1 140" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor])

/-- info: "[(some 50), (some 50), (some 50)] [48, 48, 48] true true true 1 139" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase, .splitBase, .fakeCert, .conflictProposals,
  .invalidBlocks, .forgedAuthor])

/-! ## Without the signature checks -/

/-- info: "[(some 52), (some 53), (some 52)] [50, 51, 50] false false true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert] (verify := false) (seed := 3))

/-- info: "[(some 2), (some 27), (some 27)] [0, 25, 25] true true false 0 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor] (verify := false))

end Node

end LeanDagTest
