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

/-- info: "[(some 51), (some 50), (some 51)] [49, 48, 49] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase])

/-- info: "[(some 51), (some 50), (some 51)] [49, 48, 49] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.splitBase])

/-- info: "[(some 51), (some 51), (some 51)] [49, 49, 49] true true true 0 2" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert])

/-- info: "[(some 45), (some 44), (some 44)] [43, 42, 42] true true true 1 2" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert] (seed := 3))

/-- info: "[(some 45), (some 45), (some 45)] [43, 43, 43] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.conflictProposals])

/-- info: "[(some 44), (some 44), (some 43)] [42, 42, 41] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks])

/-- info: "[(some 49), (some 50), (some 49)] [48, 48, 47] true true true 1 140" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor])

/-- info: "[(some 48), (some 48), (some 49)] [46, 46, 47] true true true 1 142" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase, .splitBase, .fakeCert, .conflictProposals,
  .invalidBlocks, .forgedAuthor])

/-! ## Without the signature checks -/

/-- info: "[(some 50), (some 50), (some 50)] [48, 48, 48] false false true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert] (verify := false) (seed := 5))

/-- info: "[(some 2), (some 32), (some 32)] [0, 30, 30] true true false 0 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor] (verify := false))

/-! ## Rate limiting

A flood: node `3` broadcasts twenty valid twins with each block. Without
rate limiting the honest stores take them; with a budget `τ = 8` and a
window `W = 8` (`docs/validator.md` §3.9) each node keeps one candidate
per author and round, and the stores stay small. Each line reads: the
slots each honest node decided, agreement, validity, the largest honest
store and the most pending blocks an honest node held. -/

/-- A scenario's outcome, with its storage. -/
def storageLine (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.commits.map (·.length)} {r.agree} {r.valid} {r.maxStore} {r.maxPending}"

/-- info: "[24, 24, 24] true true 57 1" -/
#guard_msgs in
#eval storageLine { horizon := 150, row := "mysticeti", adv := [3], attacks := [.flood] }

/-- info: "[22, 22, 22] true true 22 3" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", adv := [3], attacks := [.flood], limit := some (8, 8) }

-- A node down from tick `40` to tick `90` rejoins under rate limiting.
/-- info: "[42, 42, 42, 42] true true 33 6" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", recover := [(1, 40, 90)], limit := some (8, 8) }

end Node

end LeanDagTest
