import LeanDagSim.Net
/-!
# Attacks, simulated

`docs/validator.md` §6, step 7.4. At the Mysticeti row with `n = 4` and
`f = 1`, node `3` runs the honest program and mounts one attack, while
node `1` is down from tick `40` to tick `90` and rejoins by bootstrap,
from the horizons, blocks and certificates its peers serve. Each line
reads: the round each honest node reached, the slots it decided, whether
two nodes that decide a slot decide it alike, whether any two nodes'
decisions are prefix-comparable, whether the honest blocks are valid,
the bootstraps made, and the inputs the signature checks dropped.

With the network checking signatures, which is what the claims over
traces assume of authentication, every attack leaves agreement,
prefix-comparability and validity intact. An attack that shows node `3`
with two blocks at one round, its own fake base or its invalid twins,
gets it excluded, and while node `1` is down the two other honest nodes
are fewer than the quorum: the run stalls until node `1` is back. Under
the invalid blocks it then advances at the pace of the round timers,
reaching round 88 by tick 600. Without the checks, a certificate of
fabricated decisions can be adopted, and with node `1` down from tick
`40` to tick `70` the joiner's decisions disagree with its peers'; and
blocks forged in an honest node's name get that node excluded as an
equivocator, so that it stalls until it recovers and bootstraps.
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

/-- info: "[(some 39), (some 39), (some 39)] [38, 38, 38] true true true 1 9" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase])

/-- info: "[(some 39), (some 39), (some 39)] [38, 38, 38] true true true 1 9" -/
#guard_msgs in
#eval attackLine (attackedBy [.splitBase])

/-- info: "[(some 50), (some 50), (some 51)] [48, 49, 49] true true true 1 3" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeCert])

/-- info: "[(some 50), (some 50), (some 50)] [48, 48, 48] true true true 1 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.conflictProposals])

/-- info: "[(some 17), (some 17), (some 17)] [16, 16, 16] true true true 0 0" -/
#guard_msgs in
#eval attackLine (attackedBy [.invalidBlocks])

/-- info: "[(some 50), (some 51), (some 50)] [49, 49, 48] true true true 1 142" -/
#guard_msgs in
#eval attackLine (attackedBy [.forgedAuthor])

/-- info: "[(some 17), (some 17), (some 16)] [16, 16, 16] true true true 0 85" -/
#guard_msgs in
#eval attackLine (attackedBy [.fakeBase, .splitBase, .fakeCert, .conflictProposals,
  .invalidBlocks, .forgedAuthor])

/-! ## A node stranded below its peers' horizon

Node `3` sends its blocks to every node but node `2`, and answers none of
node `2`'s requests; messages to and from node `2` take twelve ticks
until tick `50`. The honest blocks of round `1` reference node `3`'s
genesis block, which node `2` asks for after its peers have pruned it.
Node `2` stays at round `1`, adopting its peers' certified decisions,
until the timer of round `1` finds it stalled a second time; it then
recovers and bootstraps (§3.6), with rate limiting or without. -/

/-- A slow node `2`, hidden from by node `3`. -/
def hidden (limit : Option (ℕ × ℕ)) : Scenario :=
  { horizon := 300, row := "mysticeti", adv := [3], attacks := [.hide], slow := [2],
    slowDelay := 12, slowUntil := some 50, limit := limit }

/-- info: "[(some 86), (some 85), (some 85)] [84, 83, 83] true true true 1 0" -/
#guard_msgs in
#eval attackLine (hidden none)

/-- info: "[(some 86), (some 86), (some 83)] [84, 84, 82] true true true 1 0" -/
#guard_msgs in
#eval attackLine (hidden (some (4, 8)))

/-! ## Without the signature checks -/

/-- info: "[(some 58), (some 58), (some 58)] [56, 56, 56] false false true 1 0" -/
#guard_msgs in
#eval attackLine { attackedBy [.fakeCert] (verify := false) with recover := [(1, 40, 70)] }

/-- info: "[(some 9), (some 16), (some 16)] [13, 14, 14] true true true 0 0" -/
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
/-- info: "[46, 46, 47, 46] true true 26 4" -/
#guard_msgs in
#eval storageLine
  { horizon := 150, row := "mysticeti", recover := [(1, 40, 90)], limit := some (8, 8) }

end Node

end LeanDagTest
