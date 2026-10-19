import LeanDag.Node.Runs.Statement
import LeanDag.Node.Local.Proof
/-!
# What a jump message gives, and where it came from

Along a run, every block a received jump message gave the node is one the
message denotes on a store whose blocks the node knew
(`Inv.derived_from`); every jump message the node sent denotes, on a
store whose blocks it knew, blocks it persisted (`Inv.jump_from`). Both
stores read alike where both hold a block above the sender's last block,
since what the honest nodes knew is identified by its hash
(`id_of_known`), so a block an honest node derived from an honest node's
jump message is one of the sender's own (`derived_persisted`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **A jump message among a step's outputs** is the step's jump. -/
theorem mem_jump_of_shape {K : Set (BlockId × Block Validator BlockId Payload)}
    {xs js : List (Output Validator BlockId Payload)}
    {fs bs : List (BlockId × Block Validator BlockId Payload)} {ds : List (ℕ × Option BlockId)}
    {gs : List ℕ} (hxs : ∀ o ∈ xs, o.isFetch) (hjs : Jumps cfg K fs js) {v1 : Validator}
    {B1 : BlockId} {v2 : Validator} {B2 : BlockId}
    (h : Output.jump v1 B1 v2 B2 ∈
      xs ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune) :
    v1 = cfg.me ∧ ∃ st : Store Validator BlockId Payload,
      jumpFills cfg.idOf st cfg.me B1 B2 = some fs ∧
      ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K := by
  simp only [List.mem_append, List.mem_map] at h
  rcases h with (((h | h) | h) | ⟨_, -, h⟩) | ⟨_, -, h⟩
  · exact absurd (hxs _ h) (by simp [Output.isFetch])
  · rcases hjs with ⟨rfl, -⟩ | ⟨B1', v2', B2', st, rfl, hF, hst⟩
    · exact absurd h List.not_mem_nil
    · simp only [jumped, List.mem_append, List.mem_map, List.mem_singleton] at h
      rcases h with ⟨_, -, h⟩ | h
      · cases h
      · cases h
        exact ⟨rfl, st, hF, hst⟩
  · simp only [built, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at h
    obtain ⟨_, -, h | h | h⟩ := h <;> cases h
  · cases h
  · cases h

/-- **What a run's jump messages gave the node**: blocks a message
denotes on a store whose blocks the node knew. -/
theorem Inv.derived_from : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    ∀ x ∈ derived cfg s is, ∃ v1 B1 v2 B2, Input.jump v1 B1 v2 B2 ∈ is ∧ v1 ≠ cfg.me ∧
      ∃ (st : Store Validator BlockId Payload) (F : List (BlockId × Block Validator BlockId Payload)),
      jumpFills cfg.idOf st v1 B1 B2 = some F ∧ x ∈ F ∧
      ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈
        K ∪ {x | x ∈ delivered cfg is} ∪ {x | x ∈ derived cfg s is} ∪
          {x | x ∈ persists (Node.run cfg s is).2}
  | [], _, _, _, _, x, hx => absurd hx List.not_mem_nil
  | i :: is, s, K, B, hi, x, hx => by
    have hsub : K ⊆ K ∪ {x | x ∈ delivered cfg (i :: is)} ∪ {x | x ∈ derived cfg s (i :: is)} ∪
        {x | x ∈ persists (Node.run cfg s (i :: is)).2} := fun y hy => Or.inl (Or.inl (Or.inl hy))
    simp only [derived] at hx
    rcases List.mem_append.mp hx with hx | hx
    · cases i with
      | jump v1 B1 v2 B2 =>
        change x ∈ jumpIn cfg s v1 B1 v2 B2 at hx
        unfold jumpIn at hx
        split at hx
        · rename_i hc
          cases hF : jumpFills cfg.idOf s.store v1 B1 B2 with
          | none => simp [hF] at hx
          | some F =>
            rw [hF, Option.getD_some] at hx
            exact ⟨v1, B1, v2, B2, List.mem_cons_self, hc.1, s.store, F, hF,
              (List.mem_filter.mp hx).1, fun j hj => hsub (hi.known j hj)⟩
        · exact absurd hx List.not_mem_nil
      | _ => exact absurd hx List.not_mem_nil
    · obtain ⟨xs, js, fs, bs, ds, gs, hxs, hjs, -, ho, hi₁⟩ := hi.step i
      obtain ⟨v1, B1, v2, B2, hin, hne, st, F, hF, hxF, hst⟩ := Inv.derived_from is hi₁ x hx
      refine ⟨v1, B1, v2, B2, List.mem_cons_of_mem _ hin, hne, st, F, hF, hxF, fun j hj => ?_⟩
      have hp : persists (Node.run cfg s (i :: is)).2 =
          fs ++ bs ++ persists (Node.run cfg (Node.step cfg s i).1 is).2 := by
        simp only [Node.run]; rw [persists_append, ho, persists_shape hxs hjs.shape]
      have := hst j hj
      rw [delivered_cons]
      simp only [derived, hp]
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append] at this ⊢
      tauto

/-- **What a run's jump messages denote**: on a store whose blocks the node
knew, blocks it persisted. -/
theorem Inv.jump_from : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    ∀ {v1 B1 v2 B2}, Output.jump v1 B1 v2 B2 ∈ (Node.run cfg s is).2 → v1 = cfg.me ∧
      ∃ (st : Store Validator BlockId Payload) (F : List (BlockId × Block Validator BlockId Payload)),
      jumpFills cfg.idOf st cfg.me B1 B2 = some F ∧
      (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈
        K ∪ {x | x ∈ delivered cfg is} ∪ {x | x ∈ derived cfg s is} ∪
          {x | x ∈ persists (Node.run cfg s is).2}) ∧
      ∀ x ∈ F, x ∈ persists (Node.run cfg s is).2
  | [], _, _, _, _, _, _, _, _, h => absurd h List.not_mem_nil
  | i :: is, s, K, B, hi, v1, B1, v2, B2, h => by
    obtain ⟨xs, js, fs, bs, ds, gs, hxs, hjs, -, ho, hi₁⟩ := hi.step i
    have hp : persists (Node.run cfg s (i :: is)).2 =
        fs ++ bs ++ persists (Node.run cfg (Node.step cfg s i).1 is).2 := by
      simp only [Node.run]; rw [persists_append, ho, persists_shape hxs hjs.shape]
    have hK : ∀ y, y ∈ K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ received cfg s i} ∪
        {x | x ∈ fs ++ bs} ∪ {x | x ∈ delivered cfg is} ∪
          {x | x ∈ derived cfg (Node.step cfg s i).1 is} ∪
            {x | x ∈ persists (Node.run cfg (Node.step cfg s i).1 is).2} →
        y ∈ K ∪ {x | x ∈ delivered cfg (i :: is)} ∪ {x | x ∈ derived cfg s (i :: is)} ∪
          {x | x ∈ persists (Node.run cfg s (i :: is)).2} := by
      intro y hy
      rw [delivered_cons]
      simp only [derived, hp]
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append] at hy ⊢
      tauto
    simp only [Node.run] at h
    rcases List.mem_append.mp h with h | h
    · rw [ho] at h
      obtain ⟨rfl, st, hF, hst⟩ := mem_jump_of_shape hxs hjs h
      refine ⟨rfl, st, fs, hF, fun j hj => ?_, fun x hx => by
        rw [hp]; exact List.mem_append_left _ (List.mem_append_left _ hx)⟩
      have := hst j hj
      exact hK _ (by simp only [Set.mem_union] at this ⊢; tauto)
    · obtain ⟨rfl, st, F, hF, hst, hFp⟩ := Inv.jump_from is hi₁ h
      refine ⟨rfl, st, F, hF, fun j hj => hK _ (hst j hj), fun x hx => ?_⟩
      rw [hp]
      exact List.mem_append_right _ (hFp x hx)

variable {H : Finset Validator} {ins : Validator → List (Input Validator BlockId Payload)}

theorem mem_knownOf {v : Validator} {x : BlockId × Block Validator BlockId Payload} :
    x ∈ K ∪ {x | x ∈ delivered (cfg.at v) (ins v)} ∪
        {x | x ∈ derived (cfg.at v) (State.init (cfg.at v)) (ins v)} ∪
          {x | x ∈ persists (runOf cfg ins v).2} → x ∈ K ∨ x ∈ knownOf cfg ins v := by
  intro h
  simp only [Set.mem_union, Set.mem_setOf_eq] at h
  simp only [knownOf, List.mem_append]
  tauto

/-- **What a node knew is identified by its hash.** -/
theorem id_of_known {v : Validator} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownOf cfg ins v) : x.1 = cfg.idOf x.2 := by
  simp only [knownOf, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact id_of_delivered hx
  · obtain ⟨v1, B1, v2, B2, -, -, st, F, hF, hxF, -⟩ :=
      Inv.derived_from (cfg := cfg.at v) (ins v) Inv.init x hx
    exact ((jumpFills_spec hF).2.2.2.2.2.2 x hxF).1
  · exact (Local.authored _ _ _ (cfg.at v) (ins v) x hx).1

/-- **A block an honest node derived from an honest node's jump message is
one of the sender's own.** -/
theorem derived_persisted (hJ : Runs.AuthenticJumps cfg H ins) (hinj : Runs.HashInjective cfg H ins)
    {v : Validator} (hv : v ∈ H) {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ derived (cfg.at v) (State.init (cfg.at v)) (ins v)) (hc : x.2.creator ∈ H) :
    x ∈ persists (runOf cfg ins x.2.creator).2 := by
  obtain ⟨v1, B1, v2, B2, hin, -, st, F, hF, hxF, hst⟩ :=
    Inv.derived_from (cfg := cfg.at v) (ins v) Inv.init x hx
  have hcr : x.2.creator = v1 := ((jumpFills_spec hF).2.2.2.2.2.2 x hxF).2
  rw [hcr] at hc ⊢
  obtain ⟨-, st₁, F₁, hF₁, hst₁, hFp⟩ :=
    Inv.jump_from (cfg := cfg.at v1) (ins v1) Inv.init (hJ v hv v1 B1 v2 B2 hin hc)
  have hF₁' : jumpFills cfg.idOf st₁ v1 B1 B2 = some F₁ := hF₁
  have hF' : jumpFills cfg.idOf st v1 B1 B2 = some F := hF
  -- the two stores hold what the two nodes knew, which the hash pins down
  have hraw : ∀ j ∈ st.ids, j ∈ st₁.ids → st.map.getD j st.junk = st₁.map.getD j st₁.junk := by
    intro j hj hj₁
    have hk := (mem_knownOf (hst j hj)).resolve_left (by simp)
    have hk₁ := (mem_knownOf (hst₁ j hj₁)).resolve_left (by simp)
    exact hinj v hv v1 hc _ hk _ hk₁ (by rw [← id_of_known hk, ← id_of_known hk₁])
  obtain ⟨hB1, -, hb, -⟩ := jumpFills_spec hF'
  obtain ⟨hB1₁, -, hb₁, -⟩ := jumpFills_spec hF₁'
  have hr : (st₁.blk B1).round = (st.blk B1).round := by
    simp only [Store.blk, lookup, atBase_round, hraw B1 hB1 hB1₁]
  have hFF := jumpFills_congr hF' hF₁' fun j hj hj₁ => by
    simp only [Store.blk, lookup]
    change atBase (st.blk B1).round (atBase st.base (st.map.getD j st.junk)) =
      atBase (st.blk B1).round (atBase st₁.base (st₁.map.getD j st₁.junk))
    rw [atBase_atBase hb, atBase_atBase (by rw [← hr]; exact hb₁), hraw j hj hj₁]
  subst hFF
  exact hFp x hxF

end Node

end LeanDag
