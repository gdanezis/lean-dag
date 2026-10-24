import LeanDag.Node.Sync.Model.Net
import LeanDag.Node.Sync.Helpers.Stream
/-!
# Sync by causal streams — the node and the network

`docs/sync.md` §4. A node has a target only for another node it has not
detected (`Clean`, `run_clean`), so its pending blocks are bounded
(`pending_subset`). A block enters a disk only by a stream or a build
(`step_disk`), and an honest node streams only what it holds; so a block
of an author outside `H` on an honest disk was first received by an
honest node from a node outside `H` (`entry`), and these blocks number at
most what honest nodes received from outside `H` (`card_outside_le`),
which a rate bound caps (`fromOutside_le`).
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable {blk : BlockId → Block Validator BlockId Payload}
variable {ev : Payload → Finset (BlockId × BlockId)} [Fintype Validator] {f : ℕ}

/-- **A clean state**: only another node not detected has a target. -/
def Clean (me : Validator) (s : State Validator BlockId) : Prop :=
  ∀ a, (s.target a).isSome → a ≠ me ∧ a ∉ s.detected

omit [DecidableEq Validator] [LinearOrder BlockId] [Fintype Validator] in
theorem init_clean (me : Validator) : Clean me (State.init : State Validator BlockId) :=
  fun _ h => by simp [State.init] at h

omit [Fintype Validator] in
theorem settle_clean {me : Validator} {s : State Validator BlockId} (hs : Clean me s)
    (S : Finset BlockId) (D : Finset Validator) : Clean me (settle s S D) := by
  intro a ha
  simp only [settle] at ha ⊢
  split_ifs at ha with hD
  · simp at ha
  · refine ⟨(hs a ?_).1, hD⟩
    cases h : s.target a with
    | none => simp [h] at ha
    | some c => rfl

theorem step_clean {me : Validator} {s : State Validator BlockId} (hs : Clean me s)
    (inp : Input Validator BlockId) : Clean me (step blk ev f me s inp) := by
  cases inp with
  | announce u t =>
    simp only [step]
    split_ifs with h
    · intro a ha
      by_cases hau : a = u
      · subst hau
        exact ⟨h.1, h.2.1⟩
      · simp only [Function.update_of_ne hau] at ha
        exact hs a ha
    · exact hs
  | chunk u L => exact settle_clean hs _ _
  | build x =>
    simp only [step]
    split_ifs
    · exact settle_clean hs _ _
    · exact hs
  | report i j =>
    simp only [step]
    split_ifs
    · exact settle_clean hs _ _
    · exact hs

theorem run_clean {me : Validator} :
    ∀ (s : State Validator BlockId) (ins : List (Input Validator BlockId)),
      Clean me s → Clean me (run blk ev f me s ins)
  | _, [], hs => hs
  | s, inp :: ins, hs => run_clean (step blk ev f me s inp) ins (step_clean hs inp)

omit [LinearOrder BlockId] in
theorem pending_subset {me : Validator} {s : State Validator BlockId}
    (hs : Clean me s) : pending s ⊆ (Finset.univ.erase me) \ s.detected := by
  intro a ha
  obtain ⟨hme, hD⟩ := hs a (Finset.mem_filter.mp ha).2
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hme, Finset.mem_univ a⟩, hD⟩

/-- **A block enters a disk only by a stream or the node's own build.** -/
theorem step_disk {me : Validator} {s : State Validator BlockId} {inp : Input Validator BlockId}
    {x : BlockId} (hx : x ∈ (step blk ev f me s inp).disk) :
    x ∈ s.disk ∨ (∃ u L, inp = .chunk u L ∧ x ∈ L) ∨ (inp = .build x ∧ (blk x).creator = me) := by
  cases inp with
  | announce u t =>
    simp only [step] at hx
    split_ifs at hx
    · exact Or.inl hx
    · exact Or.inl hx
  | chunk u L =>
    simp only [step, settle] at hx
    rcases Finset.mem_union.mp (absorb_sub _ _ hx) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨u, L, rfl, List.mem_of_mem_filter (List.mem_toFinset.mp h)⟩)
  | build y =>
    simp only [step] at hx
    split_ifs at hx with h
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr (Or.inr ⟨rfl, h.1⟩)
      · exact Or.inl hx
    · exact Or.inl hx
  | report i j =>
    simp only [step] at hx
    split_ifs at hx
    · exact Or.inl hx
    · exact Or.inl hx

theorem stateBefore_zero (tr : Trace Validator BlockId) (v : Validator) :
    stateBefore blk ev f tr 0 v = State.init := by
  simp [stateBefore, inputsOf, run]

theorem stateBefore_succ (tr : Trace Validator BlockId) (i : ℕ) (v : Validator) :
    stateBefore blk ev f tr (i + 1) v =
      match tr[i]? with
      | some (w, inp) => if w = v then step blk ev f v (stateBefore blk ev f tr i v) inp
          else stateBefore blk ev f tr i v
      | none => stateBefore blk ev f tr i v := by
  unfold stateBefore inputsOf run
  rw [List.take_add_one, List.filterMap_append, List.foldl_append]
  cases h : tr[i]? with
  | none => simp
  | some e =>
    obtain ⟨w, inp⟩ := e
    by_cases hw : w = v
    · simp [hw]
    · simp [hw]

/-- **The entry lemma**: a block of an author outside `H` on an honest
disk was received by an honest node from a node outside `H` before. -/
theorem entry {H : Finset Validator} {tr : Trace Validator BlockId}
    (hfaith : Faithful blk ev f H tr) :
    ∀ i, ∀ v ∈ H, ∀ x ∈ (stateBefore blk ev f tr i v).disk, (blk x).creator ∉ H →
      ∃ j < i, ∃ w ∈ H, ∃ u ∈ Hᶜ, x ∈ chunkBlocks tr j w u
  | 0, v, _, x, hx, _ => by simp [stateBefore_zero, State.init] at hx
  | i + 1, v, hv, x, hx, hxH => by
    rw [stateBefore_succ] at hx
    cases he : tr[i]? with
    | none =>
      rw [he] at hx
      obtain ⟨j, hj, rest⟩ := entry hfaith i v hv x hx hxH
      exact ⟨j, by omega, rest⟩
    | some e =>
      obtain ⟨w, inp⟩ := e
      rw [he] at hx
      simp only at hx
      split_ifs at hx with hw
      · subst hw
        rcases step_disk hx with hx | ⟨u, L, rfl, hxL⟩ | ⟨rfl, hxc⟩
        · obtain ⟨j, hj, rest⟩ := entry hfaith i w hv x hx hxH
          exact ⟨j, by omega, rest⟩
        · by_cases hu : u ∈ H
          · obtain ⟨j, hj, rest⟩ :=
              entry hfaith i u hu x (hfaith i w u L he hv hu x hxL) hxH
            exact ⟨j, by omega, rest⟩
          · refine ⟨i, by omega, w, hv, u, Finset.mem_compl.mpr hu, ?_⟩
            simp [chunkBlocks, he, hxL]
        · exact absurd (hxc ▸ hv) hxH
      · obtain ⟨j, hj, rest⟩ := entry hfaith i v hv x hx hxH
        exact ⟨j, by omega, rest⟩

omit [Fintype Validator] in
theorem card_chunkBlocks_le (tr : Trace Validator BlockId) (j : ℕ) (w u : Validator) :
    (chunkBlocks tr j w u).card ≤ chunkLen tr j w u := by
  unfold chunkBlocks chunkLen
  cases tr[j]? with
  | none => simp
  | some e =>
    obtain ⟨v, inp⟩ := e
    cases inp with
    | announce => simp
    | build => simp
    | report => simp
    | chunk u' L =>
      simp only
      split_ifs
      · exact List.toFinset_card_le L
      · simp

/-- **No amplification**: the blocks of authors outside `H` on an honest
disk number at most the blocks honest nodes received from outside `H`. -/
theorem card_outside_le {H : Finset Validator}
    {tr : Trace Validator BlockId} (hfaith : Faithful blk ev f H tr) {v : Validator} (hv : v ∈ H)
    (i : ℕ) :
    ((stateBefore blk ev f tr i v).disk.filter fun x => (blk x).creator ∉ H).card ≤
      fromOutside H tr i := by
  have hsub : ((stateBefore blk ev f tr i v).disk.filter fun x => (blk x).creator ∉ H) ⊆
      (Finset.range i).biUnion fun j => H.biUnion fun w => Hᶜ.biUnion fun u =>
        chunkBlocks tr j w u := by
    intro x hx
    obtain ⟨hxd, hxH⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj, w, hw, u, hu, hxj⟩ := entry hfaith i v hv x hxd hxH
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
      Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_biUnion.mpr ⟨u, hu, hxj⟩⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun j _ => Finset.card_biUnion_le.trans ?_
  refine Finset.sum_le_sum fun w _ => Finset.card_biUnion_le.trans ?_
  exact Finset.sum_le_sum fun u _ => card_chunkBlocks_le tr j w u

omit [LinearOrder BlockId] [Fintype Validator] in
theorem chunkLen_of_ge {tr : Trace Validator BlockId} {j : ℕ} (hj : tr.length ≤ j)
    (w u : Validator) : chunkLen tr j w u = 0 := by
  simp [chunkLen, List.getElem?_eq_none hj]

omit [LinearOrder BlockId] in
/-- **The rate bound**: by time `t`, the blocks honest nodes received
from outside `H` number at most `|H| · |Hᶜ| · k · (t + 1)`. -/
theorem fromOutside_le {H : Finset Validator}
    {tr : Trace Validator BlockId} {time : ℕ → ℕ} {k t i : ℕ}
    (hrate : RateBounded H tr time k) (ht : ∀ j < i, time j ≤ t) :
    fromOutside H tr i ≤ H.card * Hᶜ.card * k * (t + 1) := by
  unfold fromOutside
  rw [Finset.sum_comm]
  have hwu : ∀ w ∈ H, ∀ u ∈ Hᶜ,
      ∑ j ∈ Finset.range i, chunkLen tr j w u ≤ k * (t + 1) := by
    intro w hw u hu
    set A := (Finset.range i).filter (· < tr.length) with hA
    have h1 : ∑ j ∈ Finset.range i, chunkLen tr j w u = ∑ j ∈ A, chunkLen tr j w u := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun j hj hjA => ?_).symm
      refine chunkLen_of_ge ?_ w u
      by_contra h
      exact hjA (Finset.mem_filter.mpr ⟨hj, by omega⟩)
    rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := A) (t := Finset.range (t + 1)) (g := time)
      (fun j hj => Finset.mem_range.mpr (Nat.lt_succ_of_le
        (ht j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))))]
    calc ∑ τ ∈ Finset.range (t + 1), ∑ j ∈ A with time j = τ, chunkLen tr j w u
        ≤ ∑ _τ ∈ Finset.range (t + 1), k := by
          refine Finset.sum_le_sum fun τ _ => le_trans ?_ (hrate τ w hw u hu)
          refine Finset.sum_le_sum_of_subset fun j hj => ?_
          obtain ⟨hjA, hjτ⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Finset.mem_filter.mp hjA).2, hjτ⟩
      _ = k * (t + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  calc ∑ w ∈ H, ∑ j ∈ Finset.range i, ∑ u ∈ Hᶜ, chunkLen tr j w u
      = ∑ w ∈ H, ∑ u ∈ Hᶜ, ∑ j ∈ Finset.range i, chunkLen tr j w u := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ ≤ ∑ _w ∈ H, ∑ _u ∈ Hᶜ, k * (t + 1) :=
        Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun u hu => hwu w hw u hu
    _ = H.card * Hᶜ.card * k * (t + 1) := by
        simp only [Finset.sum_const, smul_eq_mul, Nat.mul_assoc]

end Sync

end Node

end LeanDag
