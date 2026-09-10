import LeanDagTest.Barnacle.Model
import LeanDag.Integration.CompRun

namespace LeanDagTest
namespace Barnacle
open LeanDag LeanDag.Integration

/-- **The composed run, at a protocol.** `Composed.genesis` at
Mysticeti's rule: one leader in every round, nothing decided, no
configuration closed. The structure is inhabited at a rule this
development actually has, not only generically. -/
noncomputable def compGenesis :
    Composed (R := bnRule.toDagRule) 4 bnP1
      (fun _ _ _ k => bnLeader k)
      (fun m b U V A => LeanDag.Barnacle.Aimd.rule bnRule bnP1 bnLeader bnWin m b U V A)
      U7 V7 0 0 :=
  Composed.genesis (R := bnRule.toDagRule) (fun _ _ _ k => bnLeader k)
    (fun m b U V A => LeanDag.Barnacle.Aimd.rule bnRule bnP1 bnLeader bnWin m b U V A)
    U7 V7 4 bnP1


end Barnacle
end LeanDagTest
