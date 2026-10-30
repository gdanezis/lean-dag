import LeanDag.Node.Local.Statement
import LeanDag.Node.Helpers.Decided
import LeanDag.Node.Helpers.SyncSteps
/-!
# An honest node, one node at a time — proof

The invariant `Inv` holds of the initial state with nothing known and no
block of its own, and each step keeps it (`Helpers/Local.lean`); the
claims about the node's own blocks and decisions are read off it at the end of a
run. The syncs keep distinct peers, none the node itself (`syncsOn_run`),
so there are at most `n − 1` (`syncs_length_le`). The decisions are the scheme's on the view by
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
  intro Validator BlockId Payload _ _ _ cfg s P _ H U V hσ hadm hfl hV hU
  have h := ViewsAbove.of_store hV hU
  letI := cfg.slots
  unfold decideStep
  dsimp only
  have hT := tryDecide_memory hσ hadm.2.1.1 s hfl (decidable cfg s.disk.topRound - 1)
  rw [h.tryDecide_eq cfg.p hadm.2.1.1 _ (Nat.zero_le _)] at hT
  split
  · rename_i hc
    rw [if_pos hc.1, commitsOf_map, hT]
  · rename_i hc
    by_cases hlt : s.lo < decidable cfg s.disk.topRound
    · rw [if_pos hlt, ← hT]
      by_contra hne
      exact hc ⟨hlt, hfl, fun h' => hne (by rw [h']; rfl)⟩
    · rw [if_neg hlt]
      rfl

theorem syncsBound : SyncsBound := by
  intro Validator BlockId Payload _ _ _ cfg is
  obtain ⟨hs, hm⟩ := syncsOn_run (cfg := cfg) is (State.init cfg)
    ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩ fun _ h => absurd h List.not_mem_nil
  exact syncs_length_le hs hm

theorem holds : Statement :=
  ⟨oneEach, authored, sends, decisions, syncsBound, validOut, decidesOnView⟩

end Local

end Node

end LeanDag
