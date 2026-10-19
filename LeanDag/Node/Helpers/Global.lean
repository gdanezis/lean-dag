import LeanDag.Node.Runs.Statement
import LeanDag.Node.Local.Proof
import LeanDag.Node.Helpers.Commits
/-!
# The run's record

The blocks the honest nodes knew, with the block map they give
(`content`), form a block record at quorum `q` whose honest set is `H`
(`globalRecord`), once two kinds of block are handled. A block is real
(`Real`) when its references are known, it is valid at `q`, and it sits
above a round the knowledge reaches (`Lives`): round `0`, or a round
holding a real block. A block that is not real keeps its round, author
and payload, and takes the references of a real block of its round
(`globalBlock`); the record holds the known blocks at rounds the
knowledge reaches. A node keeps a block at its horizon without checking
its references, so a Byzantine block there need not be real; the cut
reads it without references, and the record reads it alike there.

The record grounds what the honest nodes knew (`ground`): a known block
valid over the record is real, and one at or below a round the record
reaches is its block, read alike at that round. Free of honest
equivocation because a block with an honest author's identity is one of
that author's own, one a round: delivered, by authentication, since what
an honest node broadcasts it persists (`Local.sends`).
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

/-- The identifiers the honest nodes knew. -/
def knownIds : Finset BlockId := H.biUnion fun v => ((knownOf cfg ins v).map Prod.fst).toFinset

open Classical in
/-- **What an identifier denotes**: the block the honest nodes knew under it. -/
noncomputable def content (id : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x ∈ knownAll cfg H ins, x.1 = id then (Classical.choose h).2 else cfg.genesis

/-- **The rounds the knowledge reaches**: round `0`, and a round holding a
known block valid at the quorum, with known references, above a round
the knowledge reaches. -/
def Lives : ℕ → Prop
  | 0 => True
  | r + 1 => ∃ j ∈ knownIds cfg H ins, (content cfg H ins j).round = r + 1 ∧
      (content cfg H ins j).refs ⊆ knownIds cfg H ins ∧
      ValidAt cfg.q Clause.none (content cfg H ins) (content cfg H ins j) ∧ Lives r

/-- **A real block**: its references known, valid at the quorum, above a
round the knowledge reaches. -/
def Real (j : BlockId) : Prop :=
  (content cfg H ins j).refs ⊆ knownIds cfg H ins ∧
    ValidAt cfg.q Clause.none (content cfg H ins) (content cfg H ins j) ∧
    Lives cfg H ins ((content cfg H ins j).round - 1)

open Classical in
/-- The references of a real block of round `r`, if any. -/
noncomputable def fillRefs : ℕ → Finset BlockId
  | 0 => ∅
  | r + 1 => if h : Lives cfg H ins (r + 1) then (content cfg H ins (Classical.choose h)).refs else ∅

open Classical in
/-- **The run's block map**: a real block as known; another with the
references of a real block of its round. -/
noncomputable def globalBlock (j : BlockId) : Block Validator BlockId Payload :=
  if Real cfg H ins j then content cfg H ins j
  else { content cfg H ins j with refs := fillRefs cfg H ins (content cfg H ins j).round }

open Classical in
/-- The known blocks at rounds the knowledge reaches. -/
noncomputable def globalIds : Finset BlockId :=
  (knownIds cfg H ins).filter fun j => Lives cfg H ins (content cfg H ins j).round

variable {cfg H ins}

open Classical in
theorem mem_globalIds {j : BlockId} :
    j ∈ globalIds cfg H ins ↔ j ∈ knownIds cfg H ins ∧ Lives cfg H ins (content cfg H ins j).round := by
  unfold globalIds
  exact Finset.mem_filter

theorem mem_knownIds {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownAll cfg H ins) : x.1 ∈ knownIds cfg H ins := by
  obtain ⟨v, hv, hx⟩ := hx
  exact Finset.mem_biUnion.mpr ⟨v, hv, List.mem_toFinset.mpr (List.mem_map_of_mem hx)⟩

/-- What a node knew is identified by its hash. -/
theorem id_of_known {v : Validator} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownOf cfg ins v) : x.1 = cfg.idOf x.2 := by
  simp only [knownOf, List.mem_append] at hx
  rcases hx with hx | hx
  · exact id_of_delivered hx
  · exact (Local.authored _ _ _ (cfg.at v) (ins v) x hx).1

theorem content_of_known (hinj : Runs.HashInjective cfg H ins)
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ knownAll cfg H ins) :
    content cfg H ins x.1 = x.2 := by
  have h : ∃ y ∈ knownAll cfg H ins, y.1 = x.1 := ⟨x, hx, rfl⟩
  unfold content
  rw [dif_pos h]
  obtain ⟨hy, hyx⟩ := Classical.choose_spec h
  obtain ⟨v, hv, hyv⟩ := hy
  obtain ⟨w, hw, hxw⟩ := hx
  exact hinj v hv w hw _ hyv x hxw (by rw [← id_of_known hyv, ← id_of_known hxw, hyx])

/-- The rounds the knowledge reaches are closed downward. -/
theorem Lives.mono : ∀ {r r' : ℕ}, r ≤ r' → Lives cfg H ins r' → Lives cfg H ins r
  | _, 0, h, _ => by rw [Nat.le_zero.mp h]; trivial
  | r, r' + 1, h, hl => by
    rcases Nat.lt_or_ge r (r' + 1) with hr | hr
    · obtain ⟨-, -, -, -, -, hl'⟩ := hl
      exact Lives.mono (by omega) hl'
    · rwa [show r = r' + 1 by omega]

theorem lives_of_real {j : BlockId} (hj : j ∈ knownIds cfg H ins) (h : Real cfg H ins j) :
    Lives cfg H ins (content cfg H ins j).round := by
  rcases hr : (content cfg H ins j).round with _ | r
  · trivial
  · have := h.2.2
    rw [hr, Nat.add_sub_cancel] at this
    exact ⟨j, hj, hr, h.1, h.2.1, this⟩

@[simp] theorem globalBlock_round (j : BlockId) :
    (globalBlock cfg H ins j).round = (content cfg H ins j).round := by
  unfold globalBlock; split <;> rfl

@[simp] theorem globalBlock_creator (j : BlockId) :
    (globalBlock cfg H ins j).creator = (content cfg H ins j).creator := by
  unfold globalBlock; split <;> rfl

/-- **The references the run reads a block with**, at a round the
knowledge reaches: known, one round below, at rounds the knowledge
reaches, and from the quorum's authors above round `0`. -/
theorem globalBlock_refs {j : BlockId} (hj : Lives cfg H ins (content cfg H ins j).round) :
    (globalBlock cfg H ins j).refs ⊆ knownIds cfg H ins ∧
      (∀ x ∈ (globalBlock cfg H ins j).refs,
        (content cfg H ins x).round + 1 = (content cfg H ins j).round ∧
          Lives cfg H ins (content cfg H ins x).round) ∧
      (0 < (content cfg H ins j).round →
        cfg.q ≤ (creatorsOf (content cfg H ins) (globalBlock cfg H ins j).refs).card) := by
  unfold globalBlock
  split
  · rename_i h
    refine ⟨h.1, fun x hx => ⟨h.2.1.predecessor x hx, ?_⟩, h.2.1.quorum⟩
    have hp := h.2.1.predecessor x hx
    have := h.2.2
    rwa [show (content cfg H ins j).round - 1 = (content cfg H ins x).round by omega] at this
  · dsimp only
    rcases hr : (content cfg H ins j).round with _ | r
    · simp [fillRefs]
    · rw [hr] at hj
      simp only [fillRefs, dif_pos hj]
      obtain ⟨-, hyr, hys, hyv, hyl⟩ := Classical.choose_spec hj
      refine ⟨hys, fun x hx => ⟨by rw [hyv.predecessor x hx, hyr], ?_⟩, fun _ => ?_⟩
      · have := hyv.predecessor x hx
        rwa [show (content cfg H ins x).round = r by omega]
      · exact hyv.quorum (by omega)

variable (hinj : Runs.HashInjective cfg H ins) (hauth : Runs.Authentic cfg H ins)

include hinj hauth in
/-- **A block the honest nodes knew with an honest author's identity is
one of that author's own.** -/
theorem mem_persists_of_known {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownAll cfg H ins) (hc : x.2.creator ∈ H) :
    x ∈ persists (runOf cfg ins x.2.creator).2 := by
  obtain ⟨v, hv, hx⟩ := hx
  simp only [knownOf, List.mem_append] at hx
  rcases hx with hx | hx
  · have := hauth v hv x hx hc
    rwa [runOf, Local.sends] at this
  · have := (Local.authored _ _ _ (cfg.at v) (ins v) x hx).2
    change x.2.creator = v at this
    rw [this]
    exact hx

/-- **One block a round**: two of a node's own blocks at one round are one. -/
theorem eq_of_persists (v : Validator) {x y : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ persists (runOf cfg ins v).2) (hy : y ∈ persists (runOf cfg ins v).2)
    (hr : x.2.round = y.2.round) : x = y := by
  have h := Local.oneEach _ _ _ (cfg.at v) (ins v)
  dsimp only at h
  have hnd : ((persists (runOf cfg ins v).2).map fun e => e.2.round).Nodup := by
    exact h.imp fun hab => ne_of_lt hab
  exact List.inj_on_of_nodup_map hnd hx hy hr

/-- A known identifier is one the honest nodes knew a block under. -/
theorem exists_of_mem_knownIds {j : BlockId} (hj : j ∈ knownIds cfg H ins) :
    ∃ x ∈ knownAll cfg H ins, x.1 = j := by
  obtain ⟨v, hv, hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
  exact ⟨x, ⟨v, hv, hx⟩, rfl⟩

include hinj hauth in
/-- **The run's record.** -/
noncomputable def globalRecord :
    BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H where
  ids := globalIds cfg H ins
  block := globalBlock cfg H ins
  complete := by
    intro i hi x hx
    obtain ⟨-, hil⟩ := mem_globalIds.mp hi
    obtain ⟨hs, hr, -⟩ := globalBlock_refs hil
    exact mem_globalIds.mpr ⟨hs hx, (hr x hx).2⟩
  valid := by
    intro i hi
    obtain ⟨-, hil⟩ := mem_globalIds.mp hi
    obtain ⟨-, hr, hq⟩ := globalBlock_refs hil
    refine ⟨fun x hx => ?_, fun h0 => ?_, trivial⟩
    · rw [globalBlock_round, globalBlock_round]
      exact (hr x hx).1
    · have hcr : creators (globalBlock cfg H ins) (globalBlock cfg H ins i) =
          creatorsOf (content cfg H ins) (globalBlock cfg H ins i).refs :=
        Finset.image_congr fun x _ => globalBlock_creator x
      rw [hcr]
      exact hq (by rwa [globalBlock_round] at h0)
  no_equivocation := by
    intro i hi j hj hc hcr hr
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hi).1
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hj).1
    simp only [globalBlock_creator, globalBlock_round, content_of_known hinj hx,
      content_of_known hinj hy] at hc hcr hr
    have hbx := mem_persists_of_known hinj hauth hx hc
    have hby := mem_persists_of_known hinj hauth hy (hcr ▸ hc)
    rw [hcr] at hbx
    exact congrArg Prod.fst (eq_of_persists _ hbx hby hr)

theorem globalBlock_atBase {j : BlockId} {G : ℕ} (hG : (content cfg H ins j).round ≤ G) :
    atBase G (globalBlock cfg H ins j) = atBase G (content cfg H ins j) := by
  unfold globalBlock
  split
  · rfl
  · simp [atBase, hG]

/-- **The record grounds what the honest nodes knew.** -/
theorem ground (hq : 0 < cfg.q) :
    Ground (globalRecord hinj hauth) (knownAll cfg H ins) cfg.q where
  real := by
    intro x hx hs hv
    have hcx := content_of_known hinj hx
    have hreal : Real cfg H ins x.1 := by
      rw [Real, hcx]
      refine ⟨fun j hj => (mem_globalIds.mp (hs hj)).1, ?_, ?_⟩
      · refine ⟨fun j hj => ?_, fun h0 => ?_, trivial⟩
        · have := hv.predecessor j hj
          simp only [globalRecord, globalBlock_round] at this
          exact this
        · have hcr : creators (content cfg H ins) x.2 =
              creators (globalRecord hinj hauth).block x.2 :=
            Finset.image_congr fun j _ => (globalBlock_creator j).symm
          rw [hcr]
          exact hv.quorum h0
      · rcases hr : x.2.round with _ | r
        · trivial
        · obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le hq (hv.quorum (by omega)))
          obtain ⟨y, hy, -⟩ := mem_creatorsOf.mp hj
          have hyr := hv.predecessor y hy
          simp only [globalRecord, globalBlock_round] at hyr
          have hyl := (mem_globalIds.mp (hs hy)).2
          rw [show (content cfg H ins y).round = r by omega] at hyl
          simpa using hyl
    refine ⟨mem_globalIds.mpr ⟨mem_knownIds hx, lives_of_real (mem_knownIds hx) hreal⟩, ?_⟩
    change globalBlock cfg H ins x.1 = x.2
    unfold globalBlock
    rw [if_pos hreal, hcx]
  base := by
    intro x hx G hxG hG
    have hcx := content_of_known hinj hx
    have hl : Lives cfg H ins G := by
      rcases hG with rfl | ⟨j, hj, hjG⟩
      · trivial
      · exact Lives.mono (by simpa [globalRecord] using hjG) (mem_globalIds.mp hj).2
    refine ⟨mem_globalIds.mpr ⟨mem_knownIds hx, Lives.mono (by rw [hcx]; exact hxG) hl⟩, ?_⟩
    change atBase G (globalBlock cfg H ins x.1) = atBase G x.2
    rw [globalBlock_atBase (by rw [hcx]; exact hxG), hcx]

/-- **A started node's store is a cut of the record.** -/
theorem isCut_init (c : Config Validator BlockId Payload) :
    IsCut (globalRecord hinj hauth) (State.init c).store :=
  fun _ h => absurd h (Finset.notMem_empty _)

end Node

end LeanDag
