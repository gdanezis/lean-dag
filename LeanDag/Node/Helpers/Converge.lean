import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.Trace
import LeanDag.Node.Helpers.Global
/-!
# The honest nodes along a trace

The blocks honest nodes knew over a trace give one block map (`gT`); an
honest node's disk reads as it at every event (`reads_before`), and no
sync's block is ever ready (`noReady_before`).
-/

namespace LeanDag

namespace Node

namespace Converge

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

variable (cfg H tr) in
open Classical in
/-- **The trace's block map**: an identifier denotes the block the honest
nodes knew under it. -/
noncomputable def gT (id : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x ∈ knownIn cfg H tr, x.1 = id then (Classical.choose h).2 else cfg.genesis

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem event_of_map {i : ℕ} {u : Validator} (h : (tr[i]?.map Prod.fst) = some u) :
    ∃ inp, tr[i]? = some (u, inp) := by
  rcases hi : tr[i]? with _ | ⟨w, inp⟩
  · rw [hi] at h; exact absurd h (by simp)
  · rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact ⟨inp, rfl⟩

/-- What honest nodes knew is identified by its hash. -/
theorem id_of_knownIn {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownIn cfg H tr) : x.1 = cfg.idOf x.2 := by
  rcases hx with ⟨j, v, inp, hj, hv, hd⟩ | ⟨i, u, hu, -, hb⟩
  · exact id_of_delivered hd
  · obtain ⟨inp, hi⟩ := event_of_map hu
    exact (Local.authored _ _ _ (cfg.at u) (inputsBefore tr (i + 1) u) x
      (persists_of_event hi hb)).1

theorem content_eq (hinj : HashInjective cfg H tr) {x y : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownIn cfg H tr) (hy : y ∈ knownIn cfg H tr) (h : x.1 = y.1) : x.2 = y.2 :=
  hinj x hx y hy (by rw [← id_of_knownIn hx, ← id_of_knownIn hy, h])

theorem gT_of_known (hinj : HashInjective cfg H tr) {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownIn cfg H tr) : gT cfg H tr x.1 = x.2 := by
  have h : ∃ y ∈ knownIn cfg H tr, y.1 = x.1 := ⟨x, hx, rfl⟩
  unfold gT
  rw [dif_pos h]
  obtain ⟨hy, hyx⟩ := Classical.choose_spec h
  rw [content_eq hinj hy hx hyx]

/-- What node `v` knew before event `i`. -/
def knownBefore (cfg : Config Validator BlockId Payload) (tr : Trace Validator BlockId Payload)
    (i : ℕ) (v : Validator) : Set (BlockId × Block Validator BlockId Payload) :=
  {x | x ∈ delivered (cfg.at v) (inputsBefore tr i v) ++
    persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2}

theorem inv_before (i : ℕ) (v : Validator) :
    Inv (cfg.at v) (stateBefore cfg tr i v) (knownBefore cfg tr i v)
      (persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2) := by
  have hi := Inv.init.run (cfg := cfg.at v) (inputsBefore tr i v)
  simp only [Set.empty_union, List.nil_append] at hi
  refine hi.mono fun x hx => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq] at hx
  simp only [knownBefore, Set.mem_setOf_eq, List.mem_append]
  exact hx

/-- **The memory reaches `voteOffset` below the top**, before every event. -/
theorem floor_before {i : ℕ} {v : Validator} {r : ℕ} (ht : (stateBefore cfg tr i v).top = some r) :
    (stateBefore cfg tr i v).floor ≤ r - cfg.p.voteOffset :=
  (inv_before i v).floor.trans ((min_le_right _ _).trans (by rw [ht]; rfl))

/-- **The memory reaches the round of the next undecided slot**, before
every event. -/
theorem floor_lo_before (i : ℕ) (v : Validator) :
    (stateBefore cfg tr i v).floor ≤ cfg.slots.slotRound (stateBefore cfg tr i v).lo :=
  (inv_before i v).floor.trans (min_le_left _ _)

theorem knownBefore_sub {v : Validator} (hv : v ∈ H) (i : ℕ) :
    knownBefore cfg tr i v ⊆ knownIn cfg H tr := by
  intro x hx
  simp only [knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨j, -, inp, hj, hd⟩ := mem_delivered_before (cfg.at v) v i hx
    exact Or.inl ⟨j, v, inp, hj, hv, hd⟩
  · obtain ⟨j, -, hjv, hx⟩ := mem_persists_before (cfg := cfg) v i hx
    exact Or.inr ⟨j, v, hjv, hv, hx⟩

/-- **What an event broadcasts its node made**, at that event or before. -/
theorem persists_of_broadcasts {i : ℕ} {u : Validator} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (u, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ broadcasts (outputsAt cfg tr i)) :
    ∃ j ≤ i, ∃ inp', tr[j]? = some (u, inp') ∧ e ∈ persists (outputsAt cfg tr j) := by
  obtain ⟨bs, ho, -⟩ := (inv_before (cfg := cfg) (tr := tr) i u).step inp
  rw [outputsAt_eq hi] at he
  rcases List.mem_append.mp (ho.2.2 e he) with he | he
  · obtain ⟨j, hj, hju, hje⟩ := mem_persists_before (cfg := cfg) u i he
    obtain ⟨inp', hj'⟩ := event_of_map hju
    exact ⟨j, hj.le, inp', hj', hje⟩
  · exact ⟨i, le_rfl, inp, hi, by rw [outputsAt_eq hi, ho.1]; exact he⟩

omit [Fintype Validator] in
/-- **A block an honest node knew from an input** was delivered to it, or
streamed. -/
theorem deliver_of_delivered {j : ℕ} {v : Validator}
    {inp : Input Validator BlockId Payload} (hj : tr[j]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ delivered (cfg.at v) [inp]) :
    ((∃ u, tr[j]? = some (v, .deliver u x.1 x.2)) ∨
      ∃ u L, tr[j]? = some (v, .stream u L) ∧ x ∈ L) ∧ x.1 = cfg.idOf x.2 := by
  have hid := id_of_delivered hx
  refine ⟨?_, hid⟩
  cases inp with
  | deliver u id b =>
    simp only [delivered, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    split at hx
    · rw [List.mem_singleton] at hx; subst hx; exact Or.inl ⟨u, hj⟩
    · exact absurd hx List.not_mem_nil
  | stream u L =>
    simp only [delivered, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    exact Or.inr ⟨u, L, hj, (List.mem_filter.mp hx).1⟩
  | _ => simp [delivered] at hx

theorem stateBefore_of_le {i : ℕ} (h : tr.length ≤ i) (v : Validator) :
    stateBefore cfg tr i v = stateBefore cfg tr tr.length v := by
  unfold stateBefore; rw [inputsBefore_of_le h]

/-- **Every honest disk reads as the trace's block map.** -/
theorem reads_before (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) (i : ℕ) :
    ReadsAs (gT cfg H tr) (stateBefore cfg tr i v).disk := fun j hj =>
  (gT_of_known hinj (knownBefore_sub hv i ((inv_before (cfg := cfg) i v).known j hj))).symm

theorem pend_before (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) (i : ℕ) :
    ∀ e ∈ (stateBefore cfg tr i v).syncs, gT cfg H tr e.2.1.1 = e.2.1.2 := fun e he =>
  gT_of_known hinj (knownBefore_sub hv i ((inv_before (cfg := cfg) i v).pend e he))

theorem step_before {a : ℕ} {v : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[a]? = some (v, inp)) :
    stateBefore cfg tr (a + 1) v = (step (cfg.at v) (stateBefore cfg tr a v) inp).1 := by
  rw [stateBefore_succ h, if_pos rfl]

theorem same_before {a : ℕ} {v : Validator} (h : ∀ inp, tr[a]? ≠ some (v, inp)) :
    stateBefore cfg tr (a + 1) v = stateBefore cfg tr a v := by
  rcases ha : tr[a]? with _ | ⟨w, inp⟩
  · rw [stateBefore_of_le (List.getElem?_eq_none_iff.mp ha),
      stateBefore_of_le (by have := List.getElem?_eq_none_iff.mp ha; omega)]
  · rw [stateBefore_succ ha, if_neg]
    rintro rfl
    exact h inp ha

/-- **No sync's block is ever ready.** -/
theorem noReady_before (v : Validator) : ∀ i, NoReady (cfg.at v) (stateBefore cfg tr i v)
  | 0 => fun e he => by simp [stateBefore, inputsBefore, run, State.init] at he
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [step_before hi]
      exact noReady_step (cfg := cfg.at v) (noReady_before v i) inp
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact noReady_before v i

end Converge

end Node

end LeanDag

namespace LeanDag

namespace Node

namespace Converge

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

section Histories

variable (hinj : HashInjective cfg H tr)
include hinj

omit hinj in
theorem causal_store (i : ℕ) (v : Validator) :
    CausalStructure (stateBefore cfg tr i v).disk.blk (stateBefore cfg tr i v).disk.ids :=
  (stateBefore cfg tr i v).disk.toRecord.causal

/-- **An honest disk holding a block reads its history as the trace
does.** -/
theorem hist_eq {v : Validator} (hv : v ∈ H) {i : ℕ} {b : BlockId}
    (hb : b ∈ (stateBefore cfg tr i v).disk.ids) :
    historyFrom (stateBefore cfg tr i v).disk.blk b = historyFrom (gT cfg H tr) b :=
  historyFrom_congr (stateBefore cfg tr i v).disk.complete (reads_before hinj hv i) hb

theorem hist_sub {v : Validator} (hv : v ∈ H) {i : ℕ} {b : BlockId}
    (hb : b ∈ (stateBefore cfg tr i v).disk.ids) :
    historyFrom (gT cfg H tr) b ⊆ (stateBefore cfg tr i v).disk.ids := by
  rw [← hist_eq hinj hv hb]
  exact (causal_store i v).history_subset_ids hb

omit hinj in
/-- **What a node holds on disk it knew.** -/
theorem stored_known {v : Validator} (hv : v ∈ H) {i : ℕ} {j : BlockId}
    (hj : j ∈ (stateBefore cfg tr i v).disk.ids) :
    (j, (stateBefore cfg tr i v).disk.blk j) ∈ knownIn cfg H tr :=
  knownBefore_sub hv i ((inv_before (cfg := cfg) i v).known j hj)

/-- **A block on an honest disk fits every honest node.** -/
theorem fits_stored {u : Validator} (hu : u ∈ H) {i : ℕ} {j : BlockId}
    (hj : j ∈ (stateBefore cfg tr i u).disk.ids) (v : Validator) :
    Fits (cfg.at v) (gT cfg H tr) (j, (stateBefore cfg tr i u).disk.blk j) := by
  set st := (stateBefore cfg tr i u).disk
  have hR := reads_before hinj hu i
  have href : ∀ k ∈ (st.blk j).refs, k ∈ st.ids := st.complete j hj
  refine fits_of_valid ⟨fun k hk => ?_, ?_⟩
  · rw [← hR k (href k hk)]
    exact st.pred j hj k hk
  · refine rowValid_congr (fun k hk => ?_) ((inv_before (cfg := cfg) i u).valid j hj)
    rw [hR k (href k hk)]
    exact ⟨rfl, rfl⟩

omit hinj in
/-- **What an event makes is on its node's disk after it.** -/
theorem persist_stored {i : ℕ} {u : Validator} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (u, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) :
    e.1 ∈ (stateBefore cfg tr (i + 1) u).disk.ids ∧
      (stateBefore cfg tr (i + 1) u).disk.blk e.1 = e.2 := by
  rw [outputsAt_eq hi] at he
  rw [step_before hi]
  exact step_persist e he

omit hinj in
/-- **What an event broadcasts is on its node's disk after it.** -/
theorem broadcast_stored {i : ℕ} {u : Validator} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (u, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ broadcasts (outputsAt cfg tr i)) :
    e.1 ∈ (stateBefore cfg tr (i + 1) u).disk.ids ∧
      (stateBefore cfg tr (i + 1) u).disk.blk e.1 = e.2 := by
  obtain ⟨j, hj, inp', hj', hje⟩ := persists_of_broadcasts hi he
  obtain ⟨h₁, h₂⟩ := persist_stored hj' hje
  have hg := grows_before (cfg := cfg) (tr := tr) u (show j + 1 ≤ i + 1 by omega)
  exact ⟨hg.1 h₁, by rw [hg.blk h₁]; exact h₂⟩

end Histories

end Converge

end Node

end LeanDag
