import LeanDag.Node.Local.Statement
import LeanDag.Node.Helpers.Local
/-!
# An honest node, one node at a time — proof

The invariant `Inv` holds of the initial state with nothing known or
broadcast, and each step keeps it (`Helpers/Local.lean`); the four claims
about broadcasts are read off it at the end of a run. Decisions read only
the view by `ViewsAlike.tryDecide_eq` at the bounded vote.
-/

namespace LeanDag

namespace Node

theorem shape : Shape := by
  intro Validator BlockId Payload _ _ _ cfg is i
  obtain ⟨bs, ds, gs, hgs, ho, -⟩ := (Inv.init.run (cfg := cfg) is).step i
  exact ⟨bs, ds, gs, hgs, ho⟩

theorem oneEach : OneEach := by
  intro Validator BlockId Payload _ _ _ cfg is
  dsimp only
  have hi := Inv.init.run (cfg := cfg) is
  simp only [List.nil_append] at hi
  rcases hi.rounds with ⟨-, hB, -⟩ | ⟨t, -, -, hB⟩
  · simp [hB]
  · have hlen := congrArg List.length hB
    rw [List.length_map, List.length_range] at hlen
    rw [hB, hlen]

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
  refine ⟨fun j hj => ?_, fun blk hblk => hv blk fun x hx => hblk x ?_⟩
  · obtain ⟨c, hc⟩ := hrefs j hj
    refine List.mem_map.mpr ⟨(j, c), ?_, rfl⟩
    simp only [Set.empty_union, Set.mem_union, Set.mem_setOf_eq] at hc
    exact List.mem_append.mpr hc
  · simp only [Set.empty_union, Set.mem_union, Set.mem_setOf_eq] at hx
    exact List.mem_append.mpr hx

theorem decidesOnView : DecidesOnView := by
  intro Validator BlockId Payload _ _ _ cfg s P _ H U V hσ hV hU
  have h := ViewsAlike.of_boundedSel (U₁ := s.store.toRecord) (V₁ := s.store.view) (V₂ := V)
    hV.symm fun i hi => (hU i hi).symm
  letI := cfg.slots
  unfold decideStep
  dsimp only
  split
  · rw [hσ, h.tryDecide_eq]
  · rfl

theorem holds : Statement := ⟨shape, oneEach, authored, validOut, decidesOnView⟩

end Node

end LeanDag
