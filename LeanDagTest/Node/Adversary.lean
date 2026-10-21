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
prefix-comparability and validity intact. An attack that shows node `3`
with two blocks at one round, its own fake base or its invalid twins,
gets it excluded, and while node `1` is down the two other honest nodes
are fewer than the quorum: the run stalls until node `1` is back. Under
the invalid blocks it then advances at the pace of the round timers,
reaching round 87 by tick 600. Without the checks, a certificate of
fabricated decisions can be adopted, and with node `1` down from tick
`40` to tick `70` the joiner's decisions disagree with its peers'; and
blocks forged in an honest node's name get that node excluded as an
equivocator, which stalls the run.
-/

namespace LeanDagTest

namespace Node

open LeanDagSim

/-- A scenario under attack: node `3` attacks, node `1` rejoins. -/
def attackedBy (as : List Attack) (verify : Bool := true) : Scenario :=
  { horizon := 150, row := "mysticeti", adv := [3], attacks := as, verify := verify,
    recover := [(1, 40, 90)] }

/-- A scenario's outcome under attack, in one line. -/
def attackLine (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.tops} {r.commits.map (·.length)} {r.agree} {r.prefixes} {r.valid} {r.boots} {r.dropped}"

/-- info: "[(some 50), (some 49), (some 49)] [48, 47, 47] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase])

/-- info: "[(some 50), (some 49), (some 49)] [48, 47, 47] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.splitBase])

/-- info: "[(some 51), (some 51), (some 52)] [50, 49, 50] true true true 1 2" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert])

/-- info: "[(some 51), (some 50), (some 51)] [49, 48, 49] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.conflictProposals])

/-- info: "[(some 17), (some 17), (some 17)] [16, 16, 16] true true true 0 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks])

/-- info: "[(some 49), (some 50), (some 49)] [48, 48, 47] true true true 0 139" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor])

/-- info: "[(some 16), (some 16), (some 17)] [16, 16, 16] true true true 0 61" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase, .splitBase, .fakeCert, .conflictProposals,
  .invalidBlocks, .forgedAuthor])

/-! ## Without the signature checks -/

/-- info: "[(some 58), (some 58), (some 58)] [56, 56, 56] false false true 1 0" -/
#guard_msgs in
#eval attackLine { attackedBy [.fakeCert] (verify := false) with recover := [(1, 40, 70)] }

/-- info: "[(some 2), (some 17), (some 16)] [13, 15, 15] true true true 0 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor] (verify := false))

/-! ## Rate limiting

A flood: node `3` broadcasts twenty valid twins with each block. Without
rate limiting the honest stores take them; with a quota `ρ = 8` and a
window `W = 8` (`docs/validator.md` §3.9) each node keeps the first block
of each author and round and drops the twins no block needs, and the
stores stay small. Each line reads: the
slots each honest node decided, agreement, validity, the largest honest
store and the most pending blocks an honest node held. -/

/-- A scenario's outcome, with its storage. -/
def storageLine (sc : Scenario) : String :=
  let r := simulate sc
  s!"{r.commits.map (·.length)} {r.agree} {r.valid} {r.maxStore} {r.maxPending}"

/-- info: "[24, 24, 24] true true 141 15" -/
#guard_msgs in
#eval storageLine { horizon := 150, row := "mysticeti", adv := [3], attacks := [.flood] }

/-- info: "[24, 24, 24] true true 18 5" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", adv := [3], attacks := [.flood], limit := some (8, 8) }

/-! A Byzantine node shows each other node its own twin of each block,
and floods twenty twins besides. With a quota of `n` blocks a slot the
honest nodes keep the twins the honest blocks need and drop the flood. -/

/-- info: "[24, 24, 24] true true 127 42" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", adv := [3], attacks := [.twinSplit, .flood] }

/-- info: "[24, 24, 24] true true 18 5" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", adv := [3], attacks := [.twinSplit, .flood],
    limit := some (4, 8) }

-- A node down from tick `40` to tick `90` rejoins under rate limiting.
/-- info: "[48, 48, 48, 48] true true 25 5" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", recover := [(1, 40, 90)], limit := some (8, 8) }

end Node

end LeanDagTest
