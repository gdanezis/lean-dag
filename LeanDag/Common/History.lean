import LeanDag.Common.CausalHistory
/-!
# Causal history as a `Finset`

`Reaches` is a `Prop`, which the DoS budgets cannot count. `history U b` is
the same relation as data: the block, its references, their references, and
so on down to genesis.

The walk and its lemmas live in `Causality.lean`, over the raw block data;
a universe supplies the `CausalStructure` they consume. This file is that
layer read at `U.block`/`U.ids`, keeping the names the rest of the
development uses.

The one lemma that does any work is `mem_history_iff`: the search is fuelled
by a step count, and a reference drops the round by one (T2), so `round + 1`
steps suffice from any block of the universe.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Everything reachable from `b` in at most `n` reference steps.

Structural in the fuel `n`, so it is computable and needs no decidability
hypothesis. Outside `U.ids` it still evaluates — to junk, like `U.block`
itself — and every statement below quantifies over ids of the universe. -/
def historyUpto (U : BlockRecord Validator BlockId Payload P honest) :
    ℕ → BlockId → Finset BlockId :=
  historyUptoFrom U.block

@[simp]
theorem historyUpto_zero (b : BlockId) : historyUpto U 0 b = {b} := rfl

theorem historyUpto_succ (n : ℕ) (b : BlockId) :
    historyUpto U (n + 1) b = insert b ((U.block b).refs.biUnion (historyUpto U n)) := rfl

theorem mem_historyUpto_succ {n : ℕ} {b i : BlockId} :
    i ∈ historyUpto U (n + 1) b ↔
      i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ historyUpto U n j :=
  mem_historyUptoFrom_succ

theorem mem_historyUpto_self {n : ℕ} {b : BlockId} : b ∈ historyUpto U n b :=
  mem_historyUptoFrom_self

/-- More fuel never loses anything. Needed because `mem_history_iff` fixes the
fuel at `round + 1` while the recursion hands out whatever is left. -/
theorem historyUpto_mono {m n : ℕ} (h : m ≤ n) (b : BlockId) :
    historyUpto U m b ⊆ historyUpto U n b :=
  historyUptoFrom_mono h b

/-- **Soundness.** Anything the fuelled search finds really is reachable. No
hypothesis on `b`: even off the universe, `historyUpto` only ever walks
references. -/
theorem reaches_of_mem_historyUpto {n : ℕ} {b i : BlockId}
    (h : i ∈ historyUpto U n b) : Reaches U b i :=
  reaches_of_mem_historyUptoFrom h

variable [P.Mechanised]

/-- **Completeness**, with the fuel accounted for. A path from `b` drops the
round by one per step (T2), so `round b` steps exhaust it — and one more is
harmless by `historyUpto_mono`.

The base case is where the round bound does its work: at round `0` a
reference would have to sit below round `0`, so `b` reaches only itself. -/
theorem mem_historyUpto_of_reaches {n : ℕ} {b i : BlockId} (hb : b ∈ U.ids)
    (hn : (U.block b).round ≤ n) (h : Reaches U b i) : i ∈ historyUpto U n b :=
  U.causal.mem_historyUpto_of_reaches hb hn h

omit [P.Mechanised] in
/-- The causal history of `b`, as a `Finset`. -/
def history (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) : Finset BlockId :=
  historyFrom U.block b

/-- **The representation is faithful** (`dos-equivocation-and-growth.md` §7 S6). For a block of the universe,
membership of `history` and reachability are the same thing. -/
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i :=
  U.causal.mem_history_iff hb

omit [P.Mechanised] in
/-- A block lies in its own causal history. -/
@[simp]
theorem mem_history_self {b : BlockId} : b ∈ history U b := mem_historyFrom_self

/-- Histories stay inside the universe. -/
theorem history_subset_ids {b : BlockId} (hb : b ∈ U.ids) : history U b ⊆ U.ids :=
  U.causal.history_subset_ids hb

/-- Histories nest along reachability — the `Finset` form of transitivity, and
what makes D12 one line. -/
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c :=
  U.causal.history_subset_of_reaches hc h

/-- The one-step unfolding: a history is its block, plus the histories of its
references. The fuel bookkeeping is what makes this need a proof rather than
`rfl` — the recursion hands out `round b` steps, and each reference wants
`round + 1` of its own, which the predecessor condition reconciles. -/
theorem mem_history_succ_iff {b : BlockId} (hb : b ∈ U.ids) {i : BlockId} :
    i ∈ history U b ↔ i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ history U j :=
  U.causal.mem_history_succ_iff hb

/-- Causal history runs downward (T2), in the `Finset` form. -/
theorem round_le_of_mem_history {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b) :
    (U.block i).round ≤ (U.block b).round :=
  U.causal.round_le_of_mem_history hb hi

/-- Nothing in a block's history sits at the block's own round except the block
itself: a reference step drops the round strictly. -/
theorem eq_of_mem_history_of_round_eq {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round = (U.block b).round) : i = b :=
  U.causal.eq_of_mem_history_of_round_eq hb hi hround

/-- **The layer one below is exactly the reference set.** Anything in `b`'s
history at round `round b - 1` is a direct reference of `b`. -/
theorem mem_refs_of_mem_history_of_round_succ {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round + 1 = (U.block b).round) :
    i ∈ (U.block b).refs :=
  U.causal.mem_refs_of_mem_history_of_round_succ hb hi hround

/-- A block's references lie in its history, one step down. -/
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b :=
  U.causal.mem_history_of_mem_refs hb hj

end LeanDag
