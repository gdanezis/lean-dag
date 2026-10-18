import LeanDag.Node.Runs.Statement
import LeanDag.Node.Local.Proof
import LeanDag.Node.Helpers.Grow
/-!
# The run's record

The blocks the honest nodes' stores hold at the end of a run, with the
block map the blocks they knew give (`globalBlock`), form a block record
at the row's validity whose honest set is `H` (`globalRecord`), while no
horizon rose: closed and valid because every store is, and free of
honest equivocation because a block with an honest author's identity is
one that author broadcast, one a round.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (cfg : Config Validator BlockId Payload) (H : Finset Validator)
variable (ins : Validator → List (Input Validator BlockId Payload))

/-- Everything the honest nodes knew. -/
def knownAll : Set (BlockId × Block Validator BlockId Payload) :=
  {x | ∃ v ∈ H, x ∈ knownOf cfg ins v}

open Classical in
/-- **The run's block map**: an identifier denotes the block the honest
nodes knew under it, read at horizon `0`. -/
noncomputable def globalBlock (id : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x ∈ knownAll cfg H ins, x.1 = id then atBase 0 (Classical.choose h).2
  else cfg.genesis

variable {cfg H ins}

/-- What a node knew is identified by its hash. -/
theorem id_of_known {v : Validator} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownOf cfg ins v) : x.1 = cfg.idOf x.2 := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hx
    cases i with
    | deliver id b =>
      simp only at hi
      split at hi
      · rename_i h
        rw [Option.some.injEq] at hi
        subst hi
        exact h
      · exact absurd hi (by simp)
    | _ => exact absurd hi (by simp)
  · exact (Local.authored _ _ _ (cfg.at v) (ins v) x hx).1

theorem globalBlock_of_known (hinj : Runs.HashInjective cfg H ins)
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ knownAll cfg H ins) :
    globalBlock cfg H ins x.1 = atBase 0 x.2 := by
  have h : ∃ y ∈ knownAll cfg H ins, y.1 = x.1 := ⟨x, hx, rfl⟩
  unfold globalBlock
  rw [dif_pos h]
  obtain ⟨hy, hyx⟩ := Classical.choose_spec h
  obtain ⟨v, hv, hyv⟩ := hy
  obtain ⟨w, hw, hxw⟩ := hx
  congr 1
  exact hinj v hv w hw _ hyv x hxw (by rw [← id_of_known hyv, ← id_of_known hxw, hyx])

/-- **What a node's last state holds it knew.** -/
theorem inv_runOf (v : Validator) :
    Inv (cfg.at v) (runOf cfg ins v).1 {x | x ∈ knownOf cfg ins v}
      (broadcasts (runOf cfg ins v).2) := by
  have hi := Inv.init.run (cfg := cfg.at v) (ins v)
  simp only [Set.empty_union, List.nil_append] at hi
  refine hi.mono fun x hx => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq] at hx
  exact List.mem_append.mpr hx

theorem known_sub {v : Validator} (hv : v ∈ H) :
    {x | x ∈ knownOf cfg ins v} ⊆ knownAll cfg H ins := fun _ hx => ⟨v, hv, hx⟩

/-- **A store at horizon `0` holding known blocks reads them as the run
does.** -/
theorem blk_eq_globalBlock (hinj : Runs.HashInjective cfg H ins)
    {st : Store Validator BlockId Payload} (hb : st.base = 0)
    (hk : ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ knownAll cfg H ins) :
    ∀ j ∈ st.ids, st.blk j = globalBlock cfg H ins j := fun j hj => by
  rw [globalBlock_of_known hinj (hk j hj)]
  simp only [Store.blk, lookup, hb]

omit [Fintype Validator] [LinearOrder BlockId] in
/-- A reference-free block at round `0` is valid at the row. -/
theorem rowValid_zero {q : ℕ} {blk : BlockId → Block Validator BlockId Payload}
    {b : Block Validator BlockId Payload} (h0 : b.round = 0) (hr : b.refs = ∅) :
    rowValid q blk b := by
  refine ⟨fun i hi => ?_, fun h => absurd h (by omega),
    ⟨fun i hi => ?_, fun h => absurd h (by omega)⟩⟩
  · rw [hr] at hi; exact absurd hi (Finset.notMem_empty i)
  · rw [hr] at hi; exact absurd hi (Finset.notMem_empty i)

/-- **A block the honest nodes knew with an honest author's identity is
one that author broadcast.** -/
theorem mem_broadcasts_of_known (hauth : Runs.Authentic cfg H ins)
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ knownAll cfg H ins)
    (hc : x.2.creator ∈ H) : x ∈ broadcasts (runOf cfg ins x.2.creator).2 := by
  obtain ⟨v, hv, hx⟩ := hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hauth v hv x hx hc
  · have := (Local.authored _ _ _ (cfg.at v) (ins v) x hx).2
    change x.2.creator = v at this
    rw [this]
    exact hx

/-- **One block a round**: two blocks a node broadcast at one round are one. -/
theorem eq_of_broadcasts (v : Validator) {x y : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ broadcasts (runOf cfg ins v).2) (hy : y ∈ broadcasts (runOf cfg ins v).2)
    (hr : x.2.round = y.2.round) : x = y := by
  have h := Local.oneEach _ _ _ (cfg.at v) (ins v)
  dsimp only at h
  have hnd : ((broadcasts (runOf cfg ins v).2).map fun e => e.2.round).Nodup := by
    unfold runOf
    rw [h]
    exact List.nodup_range
  exact List.inj_on_of_nodup_map hnd hx hy hr

variable (cfg H ins) in
/-- The blocks the honest nodes' stores end with. -/
def globalIds : Finset BlockId := H.biUnion fun v => (runOf cfg ins v).1.store.ids

/-- **The run's record**, while no horizon rose. -/
noncomputable def globalRecord (hinj : Runs.HashInjective cfg H ins)
    (hauth : Runs.Authentic cfg H ins) (hbase : ∀ v ∈ H, (runOf cfg ins v).1.store.base = 0) :
    BlockRecord Validator BlockId Payload (rowValid cfg.q) H where
  ids := globalIds cfg H ins
  block := globalBlock cfg H ins
  complete := by
    intro i hi j hj
    obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp hi
    have hk := fun j hj => known_sub hv ((inv_runOf (cfg := cfg) (ins := ins) v).known j hj)
    rw [← blk_eq_globalBlock hinj (hbase v hv) hk i hiv] at hj
    exact Finset.mem_biUnion.mpr ⟨v, hv, (runOf cfg ins v).1.store.complete i hiv j hj⟩
  valid := by
    intro i hi
    obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp hi
    have hI := inv_runOf (cfg := cfg) (ins := ins) v
    have hk := fun j hj => known_sub hv (hI.known j hj)
    have hag := blk_eq_globalBlock hinj (hbase v hv) hk
    set st := (runOf cfg ins v).1.store
    rw [← hag i hiv]
    by_cases h0 : st.base < (st.map.getD i st.junk).round
    · rw [Store.blk_of_lt h0]
      refine rowValid_congr (fun j hj => ?_) (hI.valid i hiv h0)
      have hj' : j ∈ st.ids :=
        st.complete i hiv j (show j ∈ (st.blk i).refs by rw [Store.blk_of_lt h0]; exact hj)
      rw [hag j hj']
      exact ⟨rfl, rfl⟩
    · have hb : st.base = 0 := hbase v hv
      have hr : (st.blk i).round = 0 := by
        simp only [Store.blk, lookup, atBase_round]; omega
      exact rowValid_zero hr (by
        simp only [Store.blk, lookup]; exact atBase_refs_of_le (by omega))
  no_equivocation := by
    intro i hi j hj hc hcr hr
    obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨w, hw, hjw⟩ := Finset.mem_biUnion.mp hj
    have hxi := known_sub hv ((inv_runOf (cfg := cfg) (ins := ins) v).known i hiv)
    have hxj := known_sub hw ((inv_runOf (cfg := cfg) (ins := ins) w).known j hjw)
    rw [globalBlock_of_known hinj hxi] at hc hcr hr
    rw [globalBlock_of_known hinj hxj] at hcr hr
    simp only [atBase_creator, atBase_round] at hc hcr hr
    have hbi := mem_broadcasts_of_known hauth hxi hc
    have hbj := mem_broadcasts_of_known hauth hxj (hcr ▸ hc)
    rw [hcr] at hbi
    exact congrArg Prod.fst (eq_of_broadcasts _ hbi hbj hr)

end Node

end LeanDag
