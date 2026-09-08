import LeanDag.Common.Block
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Union

/-!
# Causal history, over the raw block data

Reachability and the finite causal cone, stated over a block assignment
and an id population rather than over a universe type, since neither
notion mentions validity, quorums, equivocation or a fault model. The
layer consumes two structural facts, packaged as `CausalStructure`:
references stay inside the population, and sit one round below their
referrer; everything else follows from those two. The Byzantine
`BlockUniverse` and the crash `Nemo.Universe` each supply one, and their
`Reaches`/`history` are this file's notions at their own data.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

/-- **The structural core of a block DAG.** A population closed under
references, whose references sit one round below. This is everything the
causal-history layer consumes of a universe — no validity beyond the
predecessor condition, no quorum, no fault model. -/
structure CausalStructure (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) : Prop where
  /-- Every referenced block is itself present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids
  /-- A reference sits in the round immediately below its referrer. -/
  refs_round : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, (blk j).round + 1 = (blk i).round

/-- One step of causal history: `j` is directly referenced by `i`. -/
def RefStepFrom (blk : BlockId → Block Validator BlockId Payload) (i j : BlockId) : Prop :=
  j ∈ (blk i).refs

/-- `ReachesFrom blk c b` — `b` lies in the causal history of `c`. -/
def ReachesFrom (blk : BlockId → Block Validator BlockId Payload) :
    BlockId → BlockId → Prop :=
  Relation.ReflTransGen (RefStepFrom blk)

namespace ReachesFrom

/-- Every block is in its own causal history. -/
@[refl]
theorem refl {c : BlockId} : ReachesFrom blk c c :=
  Relation.ReflTransGen.refl

/-- A direct reference is one step of causal history. -/
theorem single {i j : BlockId} (h : j ∈ (blk i).refs) : ReachesFrom blk i j :=
  Relation.ReflTransGen.single h

/-- Causal history composes. -/
theorem trans {a b c : BlockId} (h₁ : ReachesFrom blk a b) (h₂ : ReachesFrom blk b c) :
    ReachesFrom blk a c :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Prepend a direct reference. -/
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (blk i).refs) (hjb : ReachesFrom blk j b) :
    ReachesFrom blk i b :=
  trans (single hij) hjb

end ReachesFrom

/-- **Causal history never leaves a reference-closed set.** Stated over any
such set, so one lemma serves both the population of a universe and the
holdings of a view. -/
theorem mem_of_reaches_of_closed {S : Finset BlockId}
    (hS : ∀ i ∈ S, ∀ j ∈ (blk i).refs, j ∈ S) {c b : BlockId}
    (hc : c ∈ S) (h : ReachesFrom blk c b) : b ∈ S := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact hS _ ih _ hstep

/-- A block with no references reaches only itself. -/
theorem eq_of_reaches_of_refs_empty {c b : BlockId} (hc : (blk c).refs = ∅)
    (h : ReachesFrom blk c b) : b = c := by
  rcases h.cases_head with heq | ⟨_, hstep, _⟩
  · exact heq.symm
  · simp [RefStepFrom, hc] at hstep

namespace CausalStructure

/-- Causal history stays inside the population. -/
theorem mem_ids_of_reaches (C : CausalStructure blk ids)
    {c b : BlockId} (hc : c ∈ ids) (h : ReachesFrom blk c b) :
    b ∈ ids :=
  mem_of_reaches_of_closed C.complete hc h

/-- **A genesis block has no references** — one would have to sit a round
below round `0`. Derived, so no validity clause is needed for it here. -/
theorem refs_empty_of_round_zero (C : CausalStructure blk ids)
    {b : BlockId} (hb : b ∈ ids) (hround : (blk b).round = 0) :
    (blk b).refs = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
  have := C.refs_round b hb j hj
  omega

/-- **Causal history runs downward in rounds.** -/
theorem round_le_of_reaches (C : CausalStructure blk ids)
    {c b : BlockId} (hc : c ∈ ids) (h : ReachesFrom blk c b) :
    (blk b).round ≤ (blk c).round := by
  induction h with
  | refl => exact le_refl _
  | tail hab hstep ih =>
      have hmid := C.mem_ids_of_reaches hc hab
      have := C.refs_round _ hmid _ hstep
      omega

/-- A block cannot reach anything strictly above it. -/
theorem not_reaches_of_round_lt (C : CausalStructure blk ids) {c b : BlockId} (hc : c ∈ ids)
    (h : (blk c).round < (blk b).round) : ¬ ReachesFrom blk c b := by
  intro hreach
  have := C.round_le_of_reaches hc hreach
  omega

end CausalStructure

/-! ## The finite cone

`historyUptoFrom` walks references with fuel, so it is structural and needs
no decidability hypothesis; `historyFrom` fixes the fuel at `round + 1`,
which `CausalStructure.mem_historyUpto_of_reaches` shows is enough. -/

variable [DecidableEq BlockId]

/-- Everything reachable from `b` in at most `n` reference steps. -/
def historyUptoFrom (blk : BlockId → Block Validator BlockId Payload) :
    ℕ → BlockId → Finset BlockId
  | 0, b => {b}
  | n + 1, b => insert b ((blk b).refs.biUnion (historyUptoFrom blk n))

@[simp]
theorem historyUptoFrom_zero (b : BlockId) : historyUptoFrom blk 0 b = {b} := rfl

theorem historyUptoFrom_succ (n : ℕ) (b : BlockId) :
    historyUptoFrom blk (n + 1) b =
      insert b ((blk b).refs.biUnion (historyUptoFrom blk n)) := rfl

theorem mem_historyUptoFrom_succ {n : ℕ} {b i : BlockId} :
    i ∈ historyUptoFrom blk (n + 1) b ↔
      i = b ∨ ∃ j ∈ (blk b).refs, i ∈ historyUptoFrom blk n j := by
  rw [historyUptoFrom_succ, Finset.mem_insert, Finset.mem_biUnion]

theorem mem_historyUptoFrom_self {n : ℕ} {b : BlockId} : b ∈ historyUptoFrom blk n b := by
  cases n with
  | zero => simp
  | succ n => exact mem_historyUptoFrom_succ.mpr (Or.inl rfl)

/-- More fuel never loses anything. -/
theorem historyUptoFrom_mono {m n : ℕ} (h : m ≤ n) (b : BlockId) :
    historyUptoFrom blk m b ⊆ historyUptoFrom blk n b := by
  induction n generalizing m b with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp h
      exact Finset.Subset.refl _
  | succ n ih =>
      intro i hi
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [historyUptoFrom_zero, Finset.mem_singleton] at hi
        exact hi ▸ mem_historyUptoFrom_self
      · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rcases mem_historyUptoFrom_succ.mp hi with rfl | ⟨j, hj, hij⟩
        · exact mem_historyUptoFrom_self
        · exact mem_historyUptoFrom_succ.mpr (Or.inr ⟨j, hj, ih (by omega) j hij⟩)

/-- **Soundness.** Anything the fuelled search finds really is reachable. -/
theorem reaches_of_mem_historyUptoFrom {n : ℕ} {b i : BlockId}
    (h : i ∈ historyUptoFrom blk n b) : ReachesFrom blk b i := by
  induction n generalizing b with
  | zero =>
      rw [historyUptoFrom_zero, Finset.mem_singleton] at h
      exact h ▸ ReachesFrom.refl
  | succ n ih =>
      rcases mem_historyUptoFrom_succ.mp h with rfl | ⟨j, hj, hij⟩
      · exact ReachesFrom.refl
      · exact ReachesFrom.of_mem_refs hj (ih hij)

/-- The causal history of `b`, as a `Finset`. -/
def historyFrom (blk : BlockId → Block Validator BlockId Payload) (b : BlockId) :
    Finset BlockId :=
  historyUptoFrom blk ((blk b).round + 1) b

/-- A block lies in its own causal history. -/
@[simp]
theorem mem_historyFrom_self {b : BlockId} : b ∈ historyFrom blk b :=
  mem_historyUptoFrom_self

namespace CausalStructure

/-- **Completeness**, with the fuel accounted for. A path drops the round by
one per step, so `round b` steps exhaust it; the base case is the derived
`refs_empty_of_round_zero`. -/
theorem mem_historyUpto_of_reaches (C : CausalStructure blk ids)
    {n : ℕ} {b i : BlockId} (hb : b ∈ ids)
    (hn : (blk b).round ≤ n) (h : ReachesFrom blk b i) :
    i ∈ historyUptoFrom blk n b := by
  induction n generalizing b with
  | zero =>
      have hrefs : (blk b).refs = ∅ := C.refs_empty_of_round_zero hb (by omega)
      rw [eq_of_reaches_of_refs_empty hrefs h]
      simp
  | succ n ih =>
      rcases h.cases_head with rfl | ⟨j, hstep, hji⟩
      · exact mem_historyUptoFrom_self
      · have hj_ids : j ∈ ids := C.complete b hb j hstep
        have hj_round := C.refs_round b hb j hstep
        exact mem_historyUptoFrom_succ.mpr (Or.inr ⟨j, hstep, ih hj_ids (by omega) hji⟩)

/-- **The representation is faithful.** For a block of the population,
membership of `historyFrom` and reachability are the same thing. -/
theorem mem_history_iff (C : CausalStructure blk ids) {b i : BlockId} (hb : b ∈ ids) :
    i ∈ historyFrom blk b ↔ ReachesFrom blk b i :=
  ⟨reaches_of_mem_historyUptoFrom, C.mem_historyUpto_of_reaches hb (by omega)⟩

/-- Histories stay inside the population. -/
theorem history_subset_ids (C : CausalStructure blk ids)
    {b : BlockId} (hb : b ∈ ids) : historyFrom blk b ⊆ ids :=
  fun _ hi => C.mem_ids_of_reaches hb ((C.mem_history_iff hb).mp hi)

/-- Histories nest along reachability. -/
theorem history_subset_of_reaches (C : CausalStructure blk ids) {c b : BlockId} (hc : c ∈ ids)
    (h : ReachesFrom blk c b) : historyFrom blk b ⊆ historyFrom blk c := by
  have hb : b ∈ ids := C.mem_ids_of_reaches hc h
  intro i hi
  exact (C.mem_history_iff hc).mpr (h.trans ((C.mem_history_iff hb).mp hi))

/-- The one-step unfolding: a history is its block, plus the histories of its
references. The predecessor condition reconciles the fuel. -/
theorem mem_history_succ_iff (C : CausalStructure blk ids)
    {b : BlockId} (hb : b ∈ ids) {i : BlockId} :
    i ∈ historyFrom blk b ↔ i = b ∨ ∃ j ∈ (blk b).refs, i ∈ historyFrom blk j := by
  rw [historyFrom, mem_historyUptoFrom_succ]
  constructor
  · rintro (rfl | ⟨j, hj, hij⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [historyFrom, C.refs_round b hb j hj]
      exact hij
  · rintro (rfl | ⟨j, hj, hij⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [historyFrom, C.refs_round b hb j hj] at hij
      exact hij

/-- Causal history runs downward, in the `Finset` form. -/
theorem round_le_of_mem_history (C : CausalStructure blk ids) {b i : BlockId} (hb : b ∈ ids)
    (hi : i ∈ historyFrom blk b) : (blk i).round ≤ (blk b).round :=
  C.round_le_of_reaches hb ((C.mem_history_iff hb).mp hi)

/-- Nothing in a block's history sits at the block's own round except the
block itself. -/
theorem eq_of_mem_history_of_round_eq (C : CausalStructure blk ids) {b i : BlockId} (hb : b ∈ ids)
    (hi : i ∈ historyFrom blk b) (hround : (blk i).round = (blk b).round) : i = b := by
  rcases (C.mem_history_succ_iff hb).mp hi with rfl | ⟨j, hj, hij⟩
  · rfl
  · exfalso
    have hj_ids : j ∈ ids := C.complete b hb j hj
    have h1 := C.refs_round b hb j hj
    have h2 := C.round_le_of_reaches hj_ids ((C.mem_history_iff hj_ids).mp hij)
    omega

/-- **The layer one below is exactly the reference set.** -/
theorem mem_refs_of_mem_history_of_round_succ (C : CausalStructure blk ids)
    {b i : BlockId} (hb : b ∈ ids)
    (hi : i ∈ historyFrom blk b) (hround : (blk i).round + 1 = (blk b).round) :
    i ∈ (blk b).refs := by
  rcases (C.mem_history_succ_iff hb).mp hi with rfl | ⟨j, hj, hij⟩
  · omega
  · have hj_ids : j ∈ ids := C.complete b hb j hj
    have h1 := C.refs_round b hb j hj
    have h2 := C.round_le_of_reaches hj_ids ((C.mem_history_iff hj_ids).mp hij)
    have : i = j := C.eq_of_mem_history_of_round_eq hj_ids hij (by omega)
    exact this ▸ hj

/-- A block's references lie in its history, one step down. -/
theorem mem_history_of_mem_refs (C : CausalStructure blk ids) {b j : BlockId} (hb : b ∈ ids)
    (hj : j ∈ (blk b).refs) : j ∈ historyFrom blk b :=
  (C.mem_history_iff hb).mpr (ReachesFrom.single hj)

end CausalStructure

end LeanDag
