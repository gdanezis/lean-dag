import LeanDag.Node.Local.Statement
import LeanDag.Node.Helpers.Decided
/-!
# An honest node, one node at a time — proof

The invariant `Inv` holds of the initial state with nothing known and no
block of its own, and each step keeps it (`Helpers/Local.lean`); the
claims about the node's own blocks and decisions are read off it at the end of a
run. Decisions read only the view by `ViewsAbove.tryDecide_eq` at the
bounded vote.
-/

namespace LeanDag

namespace Node

namespace Local

theorem oneEach : OneEach := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  rcases hi.rounds with ⟨-, hB, -⟩ | ⟨t, -, -, hB⟩
  · simp [hB]
  · exact hB.1

theorem authored : Authored := by
  intro Validator BlockId Payload _ _ _ cfg is e he
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  exact ⟨(hi.good e he).1, (hi.good e he).2.1⟩

theorem sends : Sends := by
  intro Validator BlockId Payload _ _ _ cfg is
  exact broadcasts_run is Inv.init

theorem decisions : Decisions := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  obtain ⟨h, hL⟩ := run_appends (cfg := cfg) is Ledger.init
  have hd : (run cfg (State.init cfg) is).1.decided = commitsOf (run cfg (State.init cfg) is).2 :=
    h.1.trans (List.nil_append _)
  refine ⟨hd, hd ▸ hL, fun k ds hp => hd ▸ h.2 k ds hp⟩

theorem validOut : ValidOut := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  intro e he
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  obtain ⟨-, -, hrefs, hv⟩ := hi.good e he
  refine ⟨fun j hj => ?_, fun blk hblk => hv blk fun x hx => hblk x ?_⟩
  · obtain ⟨c, hc⟩ := hrefs j hj
    refine List.mem_map.mpr ⟨(j, c), ?_, rfl⟩
    simp only [Set.empty_union, Set.mem_union, Set.mem_setOf_eq] at hc
    simpa only [List.mem_append, or_assoc] using hc
  · simp only [Set.empty_union, Set.mem_union, Set.mem_setOf_eq] at hx
    simpa only [List.mem_append, or_assoc] using hx

theorem decidesOnView : DecidesOnView := by
  intro Validator BlockId Payload _ _ _ cfg s P _ H U V hσ hadm hlo hV hU
  have h := ViewsAbove.of_store hV hU
  letI := cfg.slots
  unfold decideStep
  dsimp only
  split
  · rw [commitsOf_append, commitsOf_map, proposeAt_commits, List.append_nil, hσ,
      h.tryDecide_eq cfg.p hadm.2.1.1 _ hlo]
  · rfl

theorem holds : Statement := ⟨oneEach, authored, sends, decisions, validOut, decidesOnView⟩

end Local

end Node

end LeanDag
