import LeanDagSim.Net
/-!
# Attacks, simulated

`docs/validator.md` §6, item 4. At the Mysticeti row with `n = 4` and
`f = 1`, node `3` runs the honest program and mounts one attack. Each
line reads: the round each honest node reached, the slots it decided,
whether two nodes that decide a slot decide it alike, whether any two
nodes' decisions are prefix-comparable, whether the honest blocks are
valid, and the inputs the signature checks dropped.

With the network checking signatures, which is what the claims over
traces assume of authentication, every attack leaves agreement,
prefix-comparability and validity intact. A node that accepts two blocks
of the attacker at one round, as with the invalid blocks' twin of its
genesis block or with twins, convicts it, takes no block from it after
and leaves it out of its references; the honest nodes then wait out the
timer at its slots, and build fewer rounds. Without the checks, the
blocks forged in node `0`'s name still reach no node: a node takes an announced block only from its author, and
the attacker streams only blocks it holds.
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

/-- info: "[(some 20), (some 20), (some 20)] [20, 20, 20] true true true 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks])

/-- info: "[(some 66), (some 66), (some 65)] [64, 64, 63] true true true 195" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor])

/-- info: "[(some 19), (some 19), (some 19)] [18, 18, 18] true true true 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.twinSplit])

/-- info: "[(some 20), (some 20), (some 19)] [18, 18, 18] true true true 69" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks, .forgedAuthor, .twinSplit])

/-! ## Without the signature checks -/

/-- info: "[(some 66), (some 66), (some 65)] [64, 64, 63] true true true 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor] (verify := false))

end Node

end LeanDagTest
