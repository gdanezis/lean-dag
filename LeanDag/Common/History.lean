import LeanDag.Common.CausalHistory
import LeanDag.Common.Support
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

/-! ## A block of a set in the anchor's cone

The indirect rules read an anchor's causal history for one of a rule's
certificates or votes: does a block of the set lie in the cone? Stated
once as reachability, with the `history` reading alongside for
decidability on data. -/

section Linked

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Some block of `s` lies in `A`'s causal history. -/
abbrev LinkedVia (U : BlockRecord Validator BlockId Payload P honest) (A : BlockId)
    (s : Finset BlockId) : Prop :=
  ∃ C ∈ s, Reaches U A C

namespace LinkedVia

variable {A B : BlockId} {s s' : Finset BlockId}

theorem of_mem {C : BlockId} (hC : C ∈ s) (h : Reaches U A C) : LinkedVia U A s := ⟨C, hC, h⟩

theorem nonempty (h : LinkedVia U A s) : s.Nonempty := by
  obtain ⟨C, hC, -⟩ := h; exact ⟨C, hC⟩

theorem mono (hs : s ⊆ s') (h : LinkedVia U A s) : LinkedVia U A s' := by
  obtain ⟨C, hC, hre⟩ := h; exact ⟨C, hs hC, hre⟩

/-- Cones nest: whatever an anchor links, everything above the anchor links. -/
theorem of_reaches (h : Reaches U B A) (hl : LinkedVia U A s) : LinkedVia U B s := by
  obtain ⟨C, hC, hre⟩ := hl; exact ⟨C, hC, h.trans hre⟩

end LinkedVia

variable [P.Mechanised]

/-- The `history` reading: decidable on data. -/
theorem linkedVia_iff_history {A : BlockId} {s : Finset BlockId} (hA : A ∈ U.ids) :
    LinkedVia U A s ↔ (s ∩ history U A).Nonempty := by
  constructor
  · rintro ⟨C, hC, hre⟩
    exact ⟨C, Finset.mem_inter.mpr ⟨hC, (mem_history_iff hA).mpr hre⟩⟩
  · rintro ⟨C, hC⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hC
    exact ⟨C, h1, (mem_history_iff hA).mp h2⟩

/-! ## Votes in an anchor's cone

The other indirect test counts, by distinct authors, the votes for a
candidate that lie in the anchor's cone — the count equivocation cannot
inflate. -/

/-- The round-`n` votes for `L` in `A`'s cone. -/
def coneVotesFor (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId) (n : ℕ) :
    Finset BlockId :=
  (votesFor U L n).filter (fun q => q ∈ history U A)

/-- The authors of the round-`n` votes for `L` in `A`'s cone. -/
def coneSupporters (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId)
    (n : ℕ) : Finset Validator :=
  creatorsOf U.block (coneVotesFor U A L n)

theorem mem_coneSupporters {A L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ coneSupporters U A L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∈ (U.block q).refs ∧
        q ∈ history U A ∧ (U.block q).creator = v := by
  simp only [coneSupporters, coneVotesFor, mem_creatorsOf, Finset.mem_filter, mem_votesFor,
    and_assoc]

/-- In-cone supporters are supporters. -/
theorem coneSupporters_subset_supporters {A L : BlockId} {n : ℕ} :
    coneSupporters U A L n ⊆ supporters U L n :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- Cones nest, so in-cone support does. -/
theorem coneSupporters_subset_of_reaches {A B L : BlockId} {n : ℕ} (hB : B ∈ U.ids)
    (h : Reaches U B A) : coneSupporters U A L n ⊆ coneSupporters U B L n := by
  refine Finset.image_subset_image fun q hq => ?_
  rw [coneVotesFor, Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, history_subset_of_reaches hB h hq.2⟩

end Linked

end LeanDag
