import LeanDag.Node.Local.Statement
import LeanDag.Node.Helpers.Decided
import LeanDag.Node.Helpers.Certify
import LeanDag.Node.Helpers.Retain
/-!
# An honest node, one node at a time — proof

The invariant `Inv` holds of the initial state with nothing known and no
block of its own, and each step keeps it (`Helpers/Local.lean`); the
claims about the node's own blocks and decisions are read off it at the end of a
run. Decisions read only the view by `ViewsAbove.tryDecide_eq` at the
bounded vote. A node certifies what it decides by `Kept`
(`Helpers/Certify.lean`): it proposed the head of its decisions at the
height and keeps the peers' proposals there, so `q` signers of the head
meet. The proposals it keeps
stay sparse (`Sparse`, `Helpers/Retain.lean`), which bounds them.
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
  have hd : (run cfg (State.init cfg) is).1.decided.reverse =
      commitsOf (run cfg (State.init cfg) is).2 :=
    h.1.trans (List.nil_append _)
  refine ⟨hd, hd ▸ hL.1, fun k kh hp => ?_⟩
  obtain ⟨hk, hkh⟩ := h.2 k kh hp
  rw [← hd, List.length_reverse]
  exact ⟨hk, hkh⟩

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
  · exact proposeAt_commits _

theorem certifies : Certifies := by
  intro Validator BlockId Payload _ _ _ cfg is k S r h hl hr hk hm hkd hme hq hS
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hK, hcov, -⟩ := Kept.run (cfg := cfg) (P := []) hl (by simp) is Kept.init Covered.init
    rfl hr (by simp)
  have hD : r.1.decided.reverse = commitsOf r.2 := (decisions Validator BlockId Payload cfg is).1
  have hlo : k ≤ r.1.lo := by
    rw [← hK.ledger.length, ← List.length_reverse, hD]; exact hkd
  -- the node proposed `k`
  have hlp : k ≤ r.1.lastProposed := by
    by_contra hlp
    exact absurd (lt_of_lt_of_le hcov (nextHeight_le hm (max_lt (not_le.mp hlp) hlt)))
      (not_lt.mpr hlo)
  have hh : ownHead cfg r.1 k = h := by unfold ownHead; rw [hD]
  -- and kept every signer's proposal
  have hpeer : ∀ u ∈ S, (u, k, h) ∈ r.1.props := by
    intro u hu
    obtain ⟨is₁, is₂, his, hw, hc⟩ := hS u hu
    have hu' : u ≠ cfg.me := fun he => hme (he ▸ hu)
    have := (kept_peer (cfg := cfg) hl hu' (his ▸ hr) hw hc).2.2
    rw [← his] at this
    exact this.resolve_right (not_le.mpr hlt)
  have hsub : insert cfg.me S ⊆ insert cfg.me (signersOf r.1.props k h) :=
    Finset.insert_subset_insert _ fun v hv => mem_signersOf.mpr (hpeer v hv)
  have hcard : cfg.q ≤ (insert cfg.me (signersOf r.1.props k (ownHead cfg r.1 k))).card := by
    rw [hh]
    exact hq.trans ((Finset.card_insert_of_notMem hme).symm.le.trans (Finset.card_le_card hsub))
  exact absurd (hK.certified k hm hlp hcard) (not_le.mpr hlt)

theorem bounded : Bounded := by
  intro Validator BlockId Payload _ _ _ cfg is s
  have h := Sparse.run (cfg := cfg) is Sparse.init
  exact ⟨h.signer_le, h.length_le⟩

theorem holds : Statement :=
  ⟨oneEach, authored, sends, decisions, validOut, decidesOnView, certifies, bounded⟩

end Local

end Node

end LeanDag
