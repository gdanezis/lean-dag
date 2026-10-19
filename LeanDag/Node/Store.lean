import LeanDag.Node.Model.Interface
/-!
# An honest node — its store

`docs/validator.md` §3.1 and §3.4. The accepted blocks, in an ordered
map, with a horizon `base`: nothing below it is kept, and a block at it
is read without references, as the cut does (`View.chop`). The store is
closed under references, and every reference sits one round below its
referrer (`stored`, the validity its record carries). `Store.insert`
accepts a block, `Store.prune` raises the horizon, and `Store.toRecord`
and `Store.view` read the store as a block record and its view.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]

section TreeMap

variable {β : Type}

omit [DecidableEq Validator] in
theorem treeMap_getD_insert_ne {t : Std.TreeMap BlockId β compare} {k a : BlockId} {fb v : β}
    (h : k ≠ a) : (t.insert k v).getD a fb = t.getD a fb := by
  rw [Std.TreeMap.getD_insert]
  simp [h]

omit [DecidableEq Validator] in
theorem treeMap_getD_filter_of {t : Std.TreeMap BlockId β compare} {f : BlockId → β → Bool}
    {k : BlockId} {fb : β} (h : f k (t.getD k fb) = true) :
    (t.filter f).getD k fb = t.getD k fb := by
  rw [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.getD_eq_getD_getElem?] at *
  rw [Std.TreeMap.getElem?_filter']
  cases hk : t[k]? with
  | none => rfl
  | some v => simp_all [Option.filter]

end TreeMap

/-- A block read at the horizon `base`: without references at or below it. -/
def atBase (base : ℕ) (b : Block Validator BlockId Payload) : Block Validator BlockId Payload :=
  if b.round ≤ base then { b with refs := ∅ } else b

omit [DecidableEq Validator] [LinearOrder BlockId] in
@[simp] theorem atBase_round (base : ℕ) (b : Block Validator BlockId Payload) :
    (atBase base b).round = b.round := by
  unfold atBase; split <;> rfl

omit [DecidableEq Validator] [LinearOrder BlockId] in
@[simp] theorem atBase_creator (base : ℕ) (b : Block Validator BlockId Payload) :
    (atBase base b).creator = b.creator := by
  unfold atBase; split <;> rfl

omit [DecidableEq Validator] [LinearOrder BlockId] in
theorem atBase_refs_of_lt {base : ℕ} {b : Block Validator BlockId Payload} (h : base < b.round) :
    (atBase base b).refs = b.refs := by
  unfold atBase; rw [if_neg (by omega)]

omit [DecidableEq Validator] [LinearOrder BlockId] in
theorem atBase_refs_of_le {base : ℕ} {b : Block Validator BlockId Payload} (h : b.round ≤ base) :
    (atBase base b).refs = ∅ := by
  unfold atBase; rw [if_pos h]

omit [DecidableEq Validator] [LinearOrder BlockId] in
theorem atBase_of_lt {G : ℕ} {b : Block Validator BlockId Payload} (h : G < b.round) :
    atBase G b = b := by
  unfold atBase; rw [if_neg (by omega)]

omit [DecidableEq Validator] [LinearOrder BlockId] in
theorem atBase_atBase {b G : ℕ} (h : b ≤ G) (x : Block Validator BlockId Payload) :
    atBase G (atBase b x) = atBase G x := by
  by_cases h₁ : x.round ≤ b
  · have h₂ : x.round ≤ G := h₁.trans h
    simp [atBase, h₁, h₂]
  · simp only [atBase, if_neg h₁]

/-- The block an identifier denotes in a map, at the horizon `base`. -/
def lookup (map : Std.TreeMap BlockId (Block Validator BlockId Payload) compare)
    (junk : Block Validator BlockId Payload) (base : ℕ) (i : BlockId) :
    Block Validator BlockId Payload :=
  atBase base (map.getD i junk)

variable (Validator BlockId Payload) in
/-- **The accepted blocks**, above the horizon `base`. -/
structure Store where
  /-- The blocks, by identifier. -/
  map : Std.TreeMap BlockId (Block Validator BlockId Payload) compare
  /-- The accepted identifiers. -/
  ids : Finset BlockId
  /-- What an identifier outside the map denotes. -/
  junk : Block Validator BlockId Payload
  /-- The horizon. -/
  base : ℕ
  /-- Every reference of an accepted block is accepted. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (lookup map junk base i).refs, j ∈ ids
  /-- Every reference sits one round below its referrer. -/
  pred : ∀ i ∈ ids, ∀ j ∈ (lookup map junk base i).refs,
    (lookup map junk base j).round + 1 = (lookup map junk base i).round
  /-- Every accepted block is at or above the horizon. -/
  above : ∀ i ∈ ids, base ≤ (lookup map junk base i).round

namespace Store

/-- The empty store at horizon `0`. -/
def empty (junk : Block Validator BlockId Payload) : Store Validator BlockId Payload where
  map := ∅
  ids := ∅
  junk := junk
  base := 0
  complete := fun _ h => absurd h (Finset.notMem_empty _)
  pred := fun _ h => absurd h (Finset.notMem_empty _)
  above := fun _ h => absurd h (Finset.notMem_empty _)

variable (s : Store Validator BlockId Payload)

/-- What each identifier denotes. -/
def blk : BlockId → Block Validator BlockId Payload := lookup s.map s.junk s.base

/-- **Accept a block**: new, at or above the horizon, and above it with
its references accepted and one round below. -/
def insert (id : BlockId) (b : Block Validator BlockId Payload) (hnew : id ∉ s.ids)
    (habove : s.base ≤ b.round) (hrefs : s.base < b.round → b.refs ⊆ s.ids)
    (hpred : s.base < b.round → ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round) :
    Store Validator BlockId Payload where
  map := s.map.insert id b
  ids := Insert.insert id s.ids
  junk := s.junk
  base := s.base
  complete := by
    have hlk : ∀ i, i ≠ id → lookup (s.map.insert id b) s.junk s.base i = s.blk i :=
      fun i hi => by simp only [lookup, blk, treeMap_getD_insert_ne (Ne.symm hi)]
    intro i hi j hj
    by_cases h : i = id
    · subst h
      simp only [lookup, Std.TreeMap.getD_insert_self] at hj
      by_cases hb : s.base < b.round
      · rw [atBase_refs_of_lt hb] at hj
        exact Finset.mem_insert_of_mem (hrefs hb hj)
      · rw [atBase_refs_of_le (by omega)] at hj
        exact absurd hj (Finset.notMem_empty _)
    · rw [hlk i h] at hj
      exact Finset.mem_insert_of_mem (s.complete i ((Finset.mem_insert.mp hi).resolve_left h) j hj)
  pred := by
    have hlk : ∀ i, i ≠ id → lookup (s.map.insert id b) s.junk s.base i = s.blk i :=
      fun i hi => by simp only [lookup, blk, treeMap_getD_insert_ne (Ne.symm hi)]
    intro i hi j hj
    by_cases h : i = id
    · subst h
      have hself : lookup (s.map.insert i b) s.junk s.base i = atBase s.base b := by
        simp only [lookup, Std.TreeMap.getD_insert_self]
      rw [hself] at hj ⊢
      by_cases hb : s.base < b.round
      · rw [atBase_refs_of_lt hb] at hj
        have hj' : j ≠ i := fun e => hnew (e ▸ hrefs hb hj)
        rw [hlk j hj', atBase_round]
        exact hpred hb j hj
      · rw [atBase_refs_of_le (by omega)] at hj
        exact absurd hj (Finset.notMem_empty _)
    · have hi' := (Finset.mem_insert.mp hi).resolve_left h
      rw [hlk i h] at hj ⊢
      have hj' : j ≠ id := fun e => hnew (e ▸ s.complete i hi' j hj)
      rw [hlk j hj']
      exact s.pred i hi' j hj
  above := by
    intro i hi
    by_cases h : i = id
    · subst h
      simp only [lookup, Std.TreeMap.getD_insert_self, atBase_round]
      exact habove
    · simp only [lookup, treeMap_getD_insert_ne (Ne.symm h)]
      exact s.above i ((Finset.mem_insert.mp hi).resolve_left h)

/-- **Raise the horizon** to `G`: drop the blocks below it, and read those
at it without references. -/
def prune (G : ℕ) (hG : s.base ≤ G) : Store Validator BlockId Payload where
  map := s.map.filter fun _ b => decide (G ≤ b.round)
  ids := s.ids.filter fun i => G ≤ (s.blk i).round
  junk := s.junk
  base := G
  complete := by
    have hraw : ∀ i, G ≤ (s.blk i).round →
        (s.map.filter fun _ b => decide (G ≤ b.round)).getD i s.junk = s.map.getD i s.junk :=
      fun i hi => treeMap_getD_filter_of (by simpa [blk, lookup] using hi)
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    simp only [lookup, hraw i hi.2] at hj
    have hround : (s.map.getD i s.junk).round = (s.blk i).round := by simp [blk, lookup]
    by_cases hb : G < (s.map.getD i s.junk).round
    · rw [atBase_refs_of_lt hb] at hj
      have hs : j ∈ (s.blk i).refs := by
        rw [blk, lookup, atBase_refs_of_lt (by omega)]; exact hj
      have hp := s.pred i hi.1 j hs
      refine Finset.mem_filter.mpr ⟨s.complete i hi.1 j hs, ?_⟩
      change (lookup s.map s.junk s.base j).round + 1 = (lookup s.map s.junk s.base i).round at hp
      change G ≤ (lookup s.map s.junk s.base j).round
      simp only [lookup, atBase_round] at hp ⊢
      omega
    · rw [atBase_refs_of_le (by omega)] at hj
      exact absurd hj (Finset.notMem_empty _)
  pred := by
    have hraw : ∀ i, G ≤ (s.blk i).round →
        (s.map.filter fun _ b => decide (G ≤ b.round)).getD i s.junk = s.map.getD i s.junk :=
      fun i hi => treeMap_getD_filter_of (by simpa [blk, lookup] using hi)
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    simp only [lookup, hraw i hi.2] at hj ⊢
    by_cases hb : G < (s.map.getD i s.junk).round
    · rw [atBase_refs_of_lt hb] at hj
      have hs : j ∈ (s.blk i).refs := by
        rw [blk, lookup, atBase_refs_of_lt (by omega)]; exact hj
      have hp := s.pred i hi.1 j hs
      change (lookup s.map s.junk s.base j).round + 1 = (lookup s.map s.junk s.base i).round at hp
      simp only [lookup, atBase_round] at hp
      have hjG : G ≤ (s.blk j).round := by simp only [blk, lookup, atBase_round]; omega
      rw [hraw j hjG, atBase_round, atBase_round]
      exact hp
    · rw [atBase_refs_of_le (by omega)] at hj
      exact absurd hj (Finset.notMem_empty _)
  above := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have h := treeMap_getD_filter_of (f := fun _ b => decide (G ≤ b.round)) (k := i)
      (fb := s.junk) (t := s.map) (by simpa [blk, lookup] using hi.2)
    simp only [lookup, h, atBase_round]
    simpa [blk, lookup] using hi.2

/-- **The store as a block record**, at `stored` and no honest set. -/
def toRecord : BlockRecord Validator BlockId Payload (stored Validator BlockId Payload) ∅ where
  ids := s.ids
  block := s.blk
  complete := s.complete
  valid := fun i hi => ⟨s.pred i hi, fun _ => Nat.zero_le _, trivial⟩
  no_equivocation := fun _ _ _ _ h => absurd h (Finset.notMem_empty _)

/-- **The node's view**: everything it accepted. -/
def view : s.toRecord.View where
  ids := s.ids
  subset_ids := subset_rfl
  complete := s.complete

/-- The highest round in the store. -/
def topRound : ℕ := s.ids.sup fun i => (s.blk i).round

end Store

end Node

end LeanDag
