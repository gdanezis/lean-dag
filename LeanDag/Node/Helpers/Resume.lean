import LeanDag.Node.Helpers.Horizon
/-!
# Resuming from what was persisted

The window lists the store's identifiers in order, each with its block,
so the map rebuilt from it gives every stored identifier its block, and
the rebuilt store meets the store's conditions because the old one did
(`resume_persisted`). The top and the own block are persisted as they are.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **Resuming from what a node persisted gives its recovered state.** -/
theorem resume_persisted {s : State Validator BlockId Payload} (hh : Held cfg s) :
    ∃ s', resume cfg s.persisted = some s' ∧
      s'.store.ids = s.store.ids ∧ s'.store.base = s.store.base ∧
      s'.store.junk = s.store.junk ∧
      (∀ j ∈ s.store.ids, s'.store.map.getD j s'.store.junk = s.store.map.getD j s.store.junk) ∧
      s' = { s.recover with store := s'.store } := by
  let st := s.store
  let w := (st.ids.sort (· ≤ ·)).map fun j => (j, st.map.getD j st.junk)
  have hfst : w.map Prod.fst = st.ids.sort (· ≤ ·) := by simp [w, List.map_map, Function.comp_def]
  have hids : (w.map Prod.fst).toFinset = st.ids := by rw [hfst, Finset.sort_toFinset]
  have hdist : w.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    have : (st.ids.sort (· ≤ ·)).Pairwise (fun a b => ¬ compare a b = .eq) :=
      (Finset.sort_nodup st.ids (· ≤ ·)).imp fun h e => h (compare_eq_iff_eq.mp e)
    exact List.pairwise_map.mpr this
  have hget : ∀ j ∈ st.ids, ∀ d,
      (Std.TreeMap.ofList w compare).getD j d = st.map.getD j st.junk := fun j hj d =>
    Std.TreeMap.getD_ofList_of_mem (k := j) (compare_eq_iff_eq.mpr rfl) hdist
      (List.mem_map.mpr ⟨j, (Finset.mem_sort _).mpr hj, rfl⟩)
  have hlk : ∀ j ∈ st.ids,
      lookup (Std.TreeMap.ofList w compare) cfg.genesis st.base j = st.blk j := fun j hj => by
    simp only [lookup, Store.blk, hget j hj]
  unfold resume
  simp only [State.persisted, Store.window]
  split
  · rename_i h
    refine ⟨_, rfl, hids, rfl, hh.junk.symm, fun j hj => hget j hj _, ?_⟩
    have hst : ∀ j ∈ st.ids, (⟨Std.TreeMap.ofList w compare, (w.map Prod.fst).toFinset,
        cfg.genesis, st.base, h.1, h.2.1, h.2.2⟩ : Store Validator BlockId Payload).blk j =
          st.blk j := hlk
    simp only [State.recover]
  · rename_i h
    refine absurd ?_ h
    rw [hids]
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_, fun i hi => ?_⟩
    · rw [hlk i hi] at hj; exact st.complete i hi j hj
    · rw [hlk i hi] at hj ⊢; rw [hlk j (st.complete i hi j hj)]; exact st.pred i hi j hj
    · rw [hlk i hi]; exact st.above i hi

end Node

end LeanDag
