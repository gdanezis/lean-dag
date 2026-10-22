import LeanDag.Node.Model.Trace
import LeanDag.Node.Local.Proof
import LeanDag.Node.Helpers.Commits
/-!
# The run's record

The blocks the honest nodes knew, with the block map they give
(`content`), form a block record at quorum `q` whose honest set is `H`
(`globalRecord`). Its blocks are the real ones (`Real`): known, with
known references, valid at `q`, and with real references. An honest node
may be delivered a Byzantine block whose references never arrive; such a
block is not real.

The record grounds what the honest nodes knew (`ground`): a known block
valid over the record is real. The record is free of honest equivocation
because a block with an honest author's identity is one of that author's
own, one a round: delivered, by authentication, since what an honest
node broadcasts it persists (`Local.sends`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (cfg : Config Validator BlockId Payload) (H : Finset Validator)
variable (tr : Trace Validator BlockId Payload)

/-- Everything the honest nodes knew. -/
def knownAll : Set (BlockId × Block Validator BlockId Payload) :=
  {x | ∃ v ∈ H, x ∈ knownOf cfg tr v}

/-- The identifiers the honest nodes knew. -/
def knownIds : Finset BlockId := H.biUnion fun v => ((knownOf cfg tr v).map Prod.fst).toFinset

open Classical in
/-- **What an identifier denotes**: the block the honest nodes knew under it. -/
noncomputable def content (id : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x ∈ knownAll cfg H tr, x.1 = id then (Classical.choose h).2 else cfg.genesis

/-- **A real block**: its references known and real, and valid at the quorum. -/
inductive Real : BlockId → Prop
  | intro {j : BlockId} : (content cfg H tr j).refs ⊆ knownIds cfg H tr →
      ValidAt cfg.q Clause.none (content cfg H tr) (content cfg H tr j) →
      (∀ x ∈ (content cfg H tr j).refs, Real x) → Real j

open Classical in
/-- The real known blocks. -/
noncomputable def globalIds : Finset BlockId :=
  (knownIds cfg H tr).filter fun j => Real cfg H tr j

/-- **Authentication at the end of the trace**: a block delivered to an
honest node with an honest author's identity is one that author
broadcast. -/
def Authentic : Prop :=
  ∀ v ∈ H, ∀ x ∈ delivered (cfg.at v) (inputsBefore tr tr.length v), x.2.creator ∈ H →
    x ∈ broadcasts (runOf cfg tr x.2.creator).2

/-- **The hash** is injective on the blocks the honest nodes knew. -/
def HashInjective : Prop :=
  ∀ v ∈ H, ∀ w ∈ H, ∀ x ∈ knownOf cfg tr v, ∀ y ∈ knownOf cfg tr w,
    cfg.idOf x.2 = cfg.idOf y.2 → x.2 = y.2

variable {cfg H tr}

open Classical in
theorem mem_globalIds {j : BlockId} :
    j ∈ globalIds cfg H tr ↔ j ∈ knownIds cfg H tr ∧ Real cfg H tr j := by
  unfold globalIds
  exact Finset.mem_filter

theorem mem_knownIds {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownAll cfg H tr) : x.1 ∈ knownIds cfg H tr := by
  obtain ⟨v, hv, hx⟩ := hx
  exact Finset.mem_biUnion.mpr ⟨v, hv, List.mem_toFinset.mpr (List.mem_map_of_mem hx)⟩

/-- What a node knew is identified by its hash. -/
theorem id_of_known {v : Validator} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownOf cfg tr v) : x.1 = cfg.idOf x.2 := by
  simp only [knownOf, List.mem_append] at hx
  rcases hx with hx | hx
  · exact id_of_delivered hx
  · exact (Local.authored _ _ _ (cfg.at v) (inputsBefore tr tr.length v) x hx).1

theorem content_of_known (hinj : HashInjective cfg H tr)
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ knownAll cfg H tr) :
    content cfg H tr x.1 = x.2 := by
  have h : ∃ y ∈ knownAll cfg H tr, y.1 = x.1 := ⟨x, hx, rfl⟩
  unfold content
  rw [dif_pos h]
  obtain ⟨hy, hyx⟩ := Classical.choose_spec h
  obtain ⟨v, hv, hyv⟩ := hy
  obtain ⟨w, hw, hxw⟩ := hx
  exact hinj v hv w hw _ hyv x hxw (by rw [← id_of_known hyv, ← id_of_known hxw, hyx])

variable (hinj : HashInjective cfg H tr) (hauth : Authentic cfg H tr)

include hinj hauth in
/-- **A block the honest nodes knew with an honest author's identity is
one of that author's own.** -/
theorem mem_persists_of_known {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownAll cfg H tr) (hc : x.2.creator ∈ H) :
    x ∈ persists (runOf cfg tr x.2.creator).2 := by
  obtain ⟨v, hv, hx⟩ := hx
  simp only [knownOf, List.mem_append] at hx
  rcases hx with hx | hx
  · have := hauth v hv x hx hc
    exact (Local.sends _ _ _ (cfg.at x.2.creator) _).2 x this
  · have := (Local.authored _ _ _ (cfg.at v) (inputsBefore tr tr.length v) x hx).2
    change x.2.creator = v at this
    rw [this]
    exact hx

/-- **One block a round**: two of a node's own blocks at one round are one. -/
theorem eq_of_persists (v : Validator) {x y : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ persists (runOf cfg tr v).2) (hy : y ∈ persists (runOf cfg tr v).2)
    (hr : x.2.round = y.2.round) : x = y := by
  have h := Local.oneEach _ _ _ (cfg.at v) (inputsBefore tr tr.length v)
  dsimp only at h
  have hnd : ((persists (runOf cfg tr v).2).map fun e => e.2.round).Nodup := by
    exact h.imp fun hab => ne_of_lt hab
  exact List.inj_on_of_nodup_map hnd hx hy hr

/-- A known identifier is one the honest nodes knew a block under. -/
theorem exists_of_mem_knownIds {j : BlockId} (hj : j ∈ knownIds cfg H tr) :
    ∃ x ∈ knownAll cfg H tr, x.1 = j := by
  obtain ⟨v, hv, hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
  exact ⟨x, ⟨v, hv, hx⟩, rfl⟩

include hinj hauth in
/-- **The run's record.** -/
noncomputable def globalRecord :
    BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H where
  ids := globalIds cfg H tr
  block := content cfg H tr
  complete := by
    intro i hi x hx
    obtain ⟨-, ⟨hs, -, hr⟩⟩ := mem_globalIds.mp hi
    exact mem_globalIds.mpr ⟨hs hx, hr x hx⟩
  valid := by
    intro i hi
    obtain ⟨-, ⟨-, hv, -⟩⟩ := mem_globalIds.mp hi
    exact hv
  no_equivocation := by
    intro i hi j hj hc hcr hr
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hi).1
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hj).1
    simp only [content_of_known hinj hx, content_of_known hinj hy] at hc hcr hr
    have hbx := mem_persists_of_known hinj hauth hx hc
    have hby := mem_persists_of_known hinj hauth hy (hcr ▸ hc)
    rw [hcr] at hbx
    exact congrArg Prod.fst (eq_of_persists _ hbx hby hr)

/-- **The record grounds what the honest nodes knew.** -/
theorem ground : Ground (globalRecord hinj hauth) (knownAll cfg H tr) cfg.q where
  real := by
    intro x hx hs hv
    have hcx := content_of_known hinj hx
    refine ⟨mem_globalIds.mpr ⟨mem_knownIds hx, ?_⟩, hcx⟩
    refine Real.intro ?_ ?_ ?_
    · rw [hcx]; exact fun j hj => (mem_globalIds.mp (hs hj)).1
    · rw [hcx]; exact hv
    · rw [hcx]; exact fun j hj => (mem_globalIds.mp (hs hj)).2

/-- **A started node's store is a cut of the record.** -/
theorem isCut_init (c : Config Validator BlockId Payload) :
    IsCut (globalRecord hinj hauth) (State.init c).store :=
  fun _ h => absurd h (Finset.notMem_empty _)

end Node

end LeanDag
