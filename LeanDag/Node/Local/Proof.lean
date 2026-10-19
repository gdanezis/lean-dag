import LeanDag.Node.Local.Statement
import LeanDag.Node.Helpers.Local
/-!
# An honest node, one node at a time — proof

The invariant `Inv` holds of the initial state with nothing known and no
block of its own, and each step keeps it (`Helpers/Local.lean`); the
four claims about the node's own blocks are read off it at the end of a
run. Decisions read only the view by `ViewsAbove.tryDecide_eq` at the
bounded vote.
-/

namespace LeanDag

namespace Node

namespace Local

theorem shape : Shape := by
  intro Validator BlockId Payload _ _ _ cfg is i
  obtain ⟨xs, js, fs, bs, ds, gs, hxs, hjs, hgs, ho, -⟩ := (Inv.init.run (cfg := cfg) is).step i
  refine ⟨xs, js, bs, ds, gs, hxs, ?_, hgs, ho⟩
  rcases hjs.shape with ⟨rfl, -⟩ | ⟨B1, v2, B2, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨fs, B1, v2, B2, rfl⟩

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

theorem validOut : ValidOut := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  intro e he
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  obtain ⟨-, -, hrefs, hv⟩ := hi.good e he
  refine ⟨fun j hj => ?_, fun hn blk hblk => hv hn blk fun x hx => hblk x ?_⟩
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
  · rw [hσ, h.tryDecide_eq cfg.p hadm.2.1.1 _ hlo]
  · rfl

theorem holds : Statement := ⟨shape, oneEach, authored, validOut, decidesOnView⟩

end Local

end Node

end LeanDag
