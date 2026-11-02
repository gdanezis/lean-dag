import LeanDag.Common.Anchored
import LeanDag.Common.Bypass
/-!
# The ledger under bypass below the decided horizon

`docs/sync-auth.md` §8. A commit of the leader `L` of slot `k` orders `L`'s
history from the top down (`layer`). A block of round `r` is ordered unless it
is already ordered, or `r + 1` lies below the round of slot `k` and the
ordered blocks of round `r + 1`, those of this commit included, bypass it.
The ledger after `n` slots is the union of the commits of slots `0, …, n - 1`
(`bypassLedger`). It reads the verdicts of the slots and the record, and no
view: the witnesses of each test are blocks already ordered.

* **Agreement** (`bypassLedger_agree_of`, `AnchoredRule.bypassLedger_agree`):
  verdicts that agree below `n` give the same ledger, and so do two
  validators that have decided every slot below `n`.
* **No retraction** (`bypassLedger_mono`), and a commit orders no block
  already ordered (`disjoint_flush`).
* **Within the committed histories** (`bypassLedger_subset_ledgerSet`).
* **Closed up to bypass** (`bypassClosed_bypassLedger`): every reference of
  an ordered block is ordered or bypassed in the ledger.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The blocks a commit of `L` orders `d` rounds below `L`, given the ordered
set `C` and the round `H` of the slot. -/
def layer (U : BlockRecord Validator BlockId Payload P honest) (q H : ℕ)
    (C : Finset BlockId) (L : BlockId) : ℕ → Finset BlockId
  | 0 => if L ∈ C then ∅ else {L}
  | d + 1 => ((layer U q H C L d).biUnion fun y => (U.block y).refs).filter fun x =>
      x ∉ C ∧ ¬ ((U.block x).round + 1 < H ∧ Bypassed U (C ∪ layer U q H C L d) q x)

/-- The blocks a commit of `L` orders. -/
def flush (U : BlockRecord Validator BlockId Payload P honest) (q H : ℕ)
    (C : Finset BlockId) (L : BlockId) : Finset BlockId :=
  (Finset.range ((U.block L).round + 1)).biUnion (layer U q H C L)

/-- The blocks ordered after slots `0, …, n - 1`, from the verdicts `g`. -/
def bypassLedger [S : Slots Validator] (U : BlockRecord Validator BlockId Payload P honest)
    (q : ℕ) (g : ℕ → Option BlockId) : ℕ → Finset BlockId
  | 0 => ∅
  | n + 1 =>
    match g n with
    | none => bypassLedger U q g n
    | some L => bypassLedger U q g n ∪ flush U q (S.slotRound n) (bypassLedger U q g n) L

theorem mem_layer_succ {q H d : ℕ} {C : Finset BlockId} {L x : BlockId} :
    x ∈ layer U q H C L (d + 1) ↔
      (∃ y ∈ layer U q H C L d, x ∈ (U.block y).refs) ∧ x ∉ C ∧
        ¬ ((U.block x).round + 1 < H ∧ Bypassed U (C ∪ layer U q H C L d) q x) := by
  simp only [layer, Finset.mem_filter, Finset.mem_biUnion]

theorem mem_flush {q H : ℕ} {C : Finset BlockId} {L x : BlockId} :
    x ∈ flush U q H C L ↔ ∃ d, d < (U.block L).round + 1 ∧ x ∈ layer U q H C L d := by
  simp [flush]

/-- A commit orders no block already ordered. -/
theorem disjoint_layer {q H : ℕ} {C : Finset BlockId} {L : BlockId} :
    ∀ d, Disjoint C (layer U q H C L d)
  | 0 => by
    unfold layer
    split_ifs with h
    · exact Finset.disjoint_empty_right _
    · exact Finset.disjoint_singleton_right.mpr h
  | d + 1 => Finset.disjoint_right.mpr fun _ hx => (mem_layer_succ.mp hx).2.1

/-- **A commit orders no block already ordered.** -/
theorem disjoint_flush {q H : ℕ} {C : Finset BlockId} {L : BlockId} :
    Disjoint C (flush U q H C L) :=
  Finset.disjoint_right.mpr fun _ hx =>
    let ⟨d, _, hd⟩ := mem_flush.mp hx
    Finset.disjoint_right.mp (disjoint_layer d) hd

/-- The blocks of a layer lie in `L`'s history. -/
theorem reaches_of_mem_layer {q H : ℕ} {C : Finset BlockId} {L : BlockId} :
    ∀ d, ∀ x ∈ layer U q H C L d, Reaches U L x
  | 0, x, hx => by
    unfold layer at hx
    split_ifs at hx
    · simp at hx
    · rw [Finset.mem_singleton.mp hx]
  | d + 1, _, hx => by
    obtain ⟨⟨y, hy, hxy⟩, -⟩ := mem_layer_succ.mp hx
    exact (reaches_of_mem_layer d y hy).trans (Reaches.single hxy)

section Ledger

variable [S : Slots Validator] {q : ℕ}

/-- **Agreement**: verdicts that agree below `n` give the same ledger. -/
theorem bypassLedger_agree_of {g₁ g₂ : ℕ → Option BlockId} :
    ∀ {n}, (∀ k, k < n → g₁ k = g₂ k) → bypassLedger U q g₁ n = bypassLedger U q g₂ n
  | 0, _ => rfl
  | n + 1, hg => by
    have ih := bypassLedger_agree_of (n := n) fun k hk => hg k (by omega)
    simp only [bypassLedger, hg n (by omega), ih]

/-- **No retraction**: the ledger only grows. -/
theorem bypassLedger_mono {g : ℕ → Option BlockId} {n m : ℕ} (h : n ≤ m) :
    bypassLedger U q g n ⊆ bypassLedger U q g m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · refine (ih (by omega)).trans ?_
      simp only [bypassLedger]
      split
      · exact subset_rfl
      · exact Finset.subset_union_left
    · exact subset_rfl

/-- **Within the committed histories**: every ordered block lies in the
history of a committed leader. -/
theorem bypassLedger_subset_ledgerSet {g : ℕ → Option BlockId} :
    ∀ {n}, ↑(bypassLedger U q g n) ⊆ ledgerSet U g n
  | 0 => by simp [bypassLedger]
  | n + 1 => by
    intro x hx
    simp only [bypassLedger] at hx
    split at hx
    · exact ledgerSet_mono (Nat.le_succ n) (bypassLedger_subset_ledgerSet hx)
    · next L hL =>
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ledgerSet_mono (Nat.le_succ n) (bypassLedger_subset_ledgerSet hx)
      · obtain ⟨d, -, hd⟩ := mem_flush.mp hx
        exact mem_ledgerSet_of_some hL (reaches_of_mem_layer d x hd)

end Ledger

section Closed

variable [P.Mechanised]

/-- A block of layer `d` lies `d` rounds below `L`. -/
theorem round_of_mem_layer {q H : ℕ} {C : Finset BlockId} {L : BlockId} (hL : L ∈ U.ids) :
    ∀ d, ∀ x ∈ layer U q H C L d, x ∈ U.ids ∧ (U.block x).round + d = (U.block L).round
  | 0, x, hx => by
    unfold layer at hx
    split_ifs at hx
    · simp at hx
    · rw [Finset.mem_singleton.mp hx]; exact ⟨hL, rfl⟩
  | d + 1, x, hx => by
    obtain ⟨⟨y, hy, hxy⟩, -⟩ := mem_layer_succ.mp hx
    obtain ⟨hyU, hyr⟩ := round_of_mem_layer hL d y hy
    have hx := BlockRecord.round_of_mem_refs hyU hxy
    exact ⟨U.complete y hyU x hxy, by omega⟩

/-- **A commit is closed up to bypass**: a reference of a block of the
commit is ordered before it, ordered by it, or bypassed in the blocks
ordered up to the round above it. -/
theorem closed_flush {q H : ℕ} {C : Finset BlockId} {L i j : BlockId} (hL : L ∈ U.ids)
    (hi : i ∈ flush U q H C L) (hj : j ∈ (U.block i).refs) :
    j ∈ C ∪ flush U q H C L ∨ Bypassed U (C ∪ flush U q H C L) q j := by
  obtain ⟨d, hd, hid⟩ := mem_flush.mp hi
  obtain ⟨hiU, hir⟩ := round_of_mem_layer hL d i hid
  have hji := BlockRecord.round_of_mem_refs hiU hj
  by_cases hjC : j ∈ C
  · exact Or.inl (Finset.mem_union_left _ hjC)
  by_cases hb : (U.block j).round + 1 < H ∧ Bypassed U (C ∪ layer U q H C L d) q j
  · refine Or.inr (hb.2.mono (Finset.union_subset_union subset_rfl fun x hx => ?_))
    exact mem_flush.mpr ⟨d, hd, hx⟩
  · refine Or.inl (Finset.mem_union_right _ (mem_flush.mpr ⟨d + 1, by omega, ?_⟩))
    exact mem_layer_succ.mpr ⟨⟨i, hid, hj⟩, hjC, hb⟩

/-- **Closed up to bypass**: if every committed leader is in the record,
every reference of an ordered block is ordered or bypassed in the ledger. -/
theorem bypassClosed_bypassLedger [S : Slots Validator] {q : ℕ} {g : ℕ → Option BlockId}
    (hg : ∀ k L, g k = some L → L ∈ U.ids) :
    ∀ n, BypassClosed U (bypassLedger U q g n) q
  | 0 => fun i hi => by simp [bypassLedger] at hi
  | n + 1 => by
    have mono : ∀ {V : Finset BlockId} {j}, V ⊆ bypassLedger U q g (n + 1) →
        j ∈ V ∨ Bypassed U V q j →
          j ∈ bypassLedger U q g (n + 1) ∨ Bypassed U (bypassLedger U q g (n + 1)) q j :=
      fun hV h => h.imp (fun h => hV h) (fun h => h.mono hV)
    intro i hi j hj
    have hsub := bypassLedger_mono (U := U) (q := q) (g := g) (Nat.le_succ n)
    rcases hn : g n with _ | L
    · simp only [bypassLedger, hn] at hi ⊢
      exact bypassClosed_bypassLedger hg n i hi j hj
    · have heq : bypassLedger U q g (n + 1) =
          bypassLedger U q g n ∪ flush U q (S.slotRound n) (bypassLedger U q g n) L := by
        simp only [bypassLedger, hn]
      rw [heq] at hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact mono hsub (bypassClosed_bypassLedger hg n i hi j hj)
      · exact mono heq.ge (closed_flush (hg n L hn) hi hj)

end Closed

namespace AnchoredRule

variable {R : AnchoredRule Validator BlockId Payload P honest} [S : Slots Validator]
variable {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}

/-- **Two validators order the same blocks under bypass**: two validators
that have decided every slot below `n` agree on the verdicts, and so on
every block ordered from the committed histories. -/
theorem bypassLedger_agree (hl : R.Laws I) (hI : I S U) {V₁ V₂ : U.View} {n q : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → R.Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → R.Decided U V₂ k (g₂ k)) :
    bypassLedger U q g₁ n = bypassLedger U q g₂ n :=
  bypassLedger_agree_of fun k hk => decided_agree hl hI (h₁ k hk) (h₂ k hk)

end AnchoredRule

end LeanDag
