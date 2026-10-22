import LeanDag.Node.Local.Statement
import LeanDag.Node.Helpers.Decided
/-!
# An honest node, one node at a time — proof

The invariant `Inv` holds of the initial state with nothing known and no
block of its own, and each step keeps it (`Helpers/Local.lean`); the
claims about the node's own blocks and decisions are read off it at the end of a
run. The decisions are the scheme's on the view by
`ViewsAbove.tryDecide_eq` at the bounded vote.
-/

namespace LeanDag

namespace Node

namespace Local

theorem oneEach : OneEach := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  rcases hi.rounds with ⟨-, hB⟩ | ⟨t, -, hB⟩
  · simp [hB]
  · exact hB.1

theorem authored : Authored := by
  intro Validator BlockId Payload _ _ _ cfg is e he
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  exact ⟨(hi.good e he).1, (hi.good e he).2.1⟩

theorem sends : Sends := by
  intro Validator BlockId Payload _ _ _ cfg is
  obtain ⟨h₁, h₂⟩ := broadcasts_run is (Inv.init (cfg := cfg))
  exact ⟨h₁, fun e he => by simpa using h₂ e he⟩

theorem decisions : Decisions := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  obtain ⟨h, hL⟩ := run_appends (cfg := cfg) is Ledger.init
  have hd : (run cfg (State.init cfg) is).1.decided.reverse =
      commitsOf (run cfg (State.init cfg) is).2 :=
    Eq.trans h (List.nil_append _)
  exact ⟨hd, hd ▸ hL⟩

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
  intro Validator BlockId Payload _ _ _ cfg s P _ H U V hσ hadm hV hU
  have h := ViewsAbove.of_store hV hU
  letI := cfg.slots
  unfold decideStep
  dsimp only
  split
  · rw [commitsOf_map, tryDecide_window cfg hσ hadm.2.1.1, hσ,
      h.tryDecide_eq cfg.p hadm.2.1.1 _ (Nat.zero_le _)]
  · rfl

theorem holds : Statement :=
  ⟨oneEach, authored, sends, decisions, validOut, decidesOnView⟩

end Local

end Node

end LeanDag
