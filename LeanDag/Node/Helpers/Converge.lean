import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.Trace
import LeanDag.Node.Helpers.Walk
import LeanDag.Node.Helpers.Global
/-!
# The honest nodes along a trace

The blocks honest nodes knew over a trace give one block map (`gT`); an
honest node's store reads as it at every event, at horizon `0`
(`reads_before`). Over time then: a block that fits stays pending or
stored (`keeps_after`); no pending block is ever ready
(`noReady_before`); a block becomes pending only by a delivery the node
acts on (`entry_before`); and a request is recorded only on account of
such a delivery (`requested_before`).
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
nodes knew under it, read at horizon `0`. -/
noncomputable def gT (id : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x ∈ knownIn cfg H tr, x.1 = id then atBase 0 (Classical.choose h).2 else cfg.genesis

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem event_of_map {i : ℕ} {u : Validator} (h : (tr[i]?.map Prod.fst) = some u) :
    ∃ inp, tr[i]? = some (u, inp) := by
  rcases hi : tr[i]? with _ | ⟨w, inp⟩
  · rw [hi] at h; exact absurd h (by simp)
  · rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact ⟨inp, rfl⟩

/-- What honest nodes knew is identified by its hash. -/
theorem id_of_knownIn {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownIn cfg H tr) : x.1 = cfg.idOf x.2 := by
  rcases hx with ⟨j, v, hj, hv, hid⟩ | ⟨i, u, hu, -, hb⟩ | ⟨i, v, -, hd⟩
  · exact hid
  · obtain ⟨inp, hi⟩ := event_of_map hu
    exact (Local.authored _ _ _ (cfg.at u) (inputsBefore tr (i + 1) u) x
      (persists_of_event hi hb)).1
  · obtain ⟨v1, B1, v2, B2, -, -, st, F, hF, hxF, -⟩ :=
      Inv.derived_from (cfg := cfg.at v) _ Inv.init x hd
    exact ((jumpFills_spec hF).2.2.2.2.2.2 x hxF).1

theorem content_eq (hinj : HashInjective cfg H tr) {x y : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownIn cfg H tr) (hy : y ∈ knownIn cfg H tr) (h : x.1 = y.1) : x.2 = y.2 :=
  hinj x hx y hy (by rw [← id_of_knownIn hx, ← id_of_knownIn hy, h])

theorem gT_of_known (hinj : HashInjective cfg H tr) {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownIn cfg H tr) : gT cfg H tr x.1 = atBase 0 x.2 := by
  have h : ∃ y ∈ knownIn cfg H tr, y.1 = x.1 := ⟨x, hx, rfl⟩
  unfold gT
  rw [dif_pos h]
  obtain ⟨hy, hyx⟩ := Classical.choose_spec h
  rw [content_eq hinj hy hx hyx]

/-- What node `v` knew before event `i`. -/
def knownBefore (cfg : Config Validator BlockId Payload) (tr : Trace Validator BlockId Payload)
    (i : ℕ) (v : Validator) : Set (BlockId × Block Validator BlockId Payload) :=
  {x | x ∈ delivered (cfg.at v) (inputsBefore tr i v) ++
    derived (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v) ++
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

theorem knownBefore_sub {v : Validator} (hv : v ∈ H) (i : ℕ) :
    knownBefore cfg tr i v ⊆ knownIn cfg H tr := by
  intro x hx
  simp only [knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨j, -, hj, hid⟩ := mem_delivered_before (cfg.at v) v i hx
    exact Or.inl ⟨j, v, hj, hv, hid⟩
  · exact Or.inr (Or.inr ⟨i, v, hv, hx⟩)
  · obtain ⟨j, -, hjv, hx⟩ := mem_persists_before (cfg := cfg) v i hx
    exact Or.inr (Or.inl ⟨j, v, hjv, hv, hx⟩)

/-- **What an event broadcasts it made.** -/
theorem persists_of_broadcasts {i : ℕ} {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ broadcasts (outputsAt cfg tr i)) : e ∈ persists (outputsAt cfg tr i) := by
  unfold outputsAt at he ⊢
  split at he
  · rename_i v inp _
    obtain ⟨xs, js, fs, bs, ds, gs, hxs, hjs, -, ho, -⟩ :=
      (inv_before (cfg := cfg) (tr := tr) i v).step inp
    rw [ho, broadcasts_shape hxs hjs.shape] at he
    rw [ho, persists_shape hxs hjs.shape]
    exact List.mem_append_right _ he
  · exact absurd he List.not_mem_nil

omit [Fintype Validator] [LinearOrder BlockId] in
theorem mem_inputsBefore {i : ℕ} {w : Validator} {x : Input Validator BlockId Payload}
    (h : x ∈ inputsBefore tr i w) : ∃ j : ℕ, tr[j]? = some (w, x) := by
  obtain ⟨e, he, hex⟩ := List.mem_filterMap.mp h
  split at hex
  · rename_i hw
    rw [Option.some.injEq] at hex
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hj
    split at hj
    · refine ⟨j, ?_⟩
      rw [hj, ← hw, ← hex]
    · cases hj
  · cases hex

/-- An input other than a jump message gives no block besides a delivered one. -/
theorem received_of_ne {c : Config Validator BlockId Payload} {s : State Validator BlockId Payload}
    {inp : Input Validator BlockId Payload} (h : ∀ v1 B1 v2 B2, inp ≠ .jump v1 B1 v2 B2) :
    received c s inp = [] := by
  cases inp with
  | jump v1 B1 v2 B2 => exact absurd rfl (h v1 B1 v2 B2)
  | _ => rfl

theorem derived_nil {c : Config Validator BlockId Payload} :
    ∀ {s : State Validator BlockId Payload} {is : List (Input Validator BlockId Payload)},
    (∀ i ∈ is, ∀ v1 B1 v2 B2, i ≠ .jump v1 B1 v2 B2) → derived c s is = []
  | _, [], _ => rfl
  | s, i :: is, h => by
    simp only [derived, received_of_ne (h i List.mem_cons_self), List.nil_append]
    exact derived_nil fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **No jump message gives an honest node a block**, when none is given one. -/
theorem derived_before (hnj : NoJump H tr) {w : Validator} (hw : w ∈ H) (i : ℕ) :
    derived (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr i w) = [] :=
  derived_nil fun x hx v1 B1 v2 B2 h => by
    obtain ⟨j, hj⟩ := mem_inputsBefore hx
    exact hnj j w v1 B1 v2 B2 hw (h ▸ hj)

theorem stateBefore_of_le {i : ℕ} (h : tr.length ≤ i) (v : Validator) :
    stateBefore cfg tr i v = stateBefore cfg tr tr.length v := by
  unfold stateBefore; rw [inputsBefore_of_le h]

/-- **Every honest store is at horizon `0`**, when the last ones are. -/
theorem base_before (hbase : ∀ v ∈ H, (stateBefore cfg tr tr.length v).store.base = 0)
    {v : Validator} (hv : v ∈ H) (i : ℕ) : (stateBefore cfg tr i v).store.base = 0 := by
  by_cases h : i ≤ tr.length
  · have := (grows_before (cfg := cfg) (tr := tr) v h).1
    rw [hbase v hv] at this
    omega
  · rw [stateBefore_of_le (by omega)]; exact hbase v hv

/-- **Every honest store reads as the trace's block map.** -/
theorem reads_before (hinj : HashInjective cfg H tr)
    (hbase : ∀ v ∈ H, (stateBefore cfg tr tr.length v).store.base = 0)
    {v : Validator} (hv : v ∈ H) (i : ℕ) :
    ReadsAs (gT cfg H tr) (stateBefore cfg tr i v).store := by
  refine ⟨base_before hbase hv i, fun j hj => ?_⟩
  have hk := knownBefore_sub hv i ((inv_before (cfg := cfg) i v).known j hj)
  rw [gT_of_known hinj hk]
  simp only [Store.blk, lookup, base_before hbase hv i]

theorem pend_before (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) (i : ℕ) :
    ∀ e ∈ (stateBefore cfg tr i v).pending, gT cfg H tr e.1 = atBase 0 e.2 := fun e he =>
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

/-- **A block that fits stays pending or stored.** -/
theorem keeps_after (hinj : HashInjective cfg H tr)
    (hbase : ∀ v ∈ H, (stateBefore cfg tr tr.length v).store.base = 0) (hnr : NoRestart H tr)
    (hnj : NoJump H tr) {v : Validator} (hv : v ∈ H) {y : BlockId × Block Validator BlockId Payload}
    (hf : Fits (cfg.at v) (gT cfg H tr) y) {a : ℕ}
    (hy : y ∈ (stateBefore cfg tr a v).pending ∨ y.1 ∈ (stateBefore cfg tr a v).store.ids) :
    ∀ b, a ≤ b →
      y ∈ (stateBefore cfg tr b v).pending ∨ y.1 ∈ (stateBefore cfg tr b v).store.ids := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact hy
  | succ j _ ih =>
    by_cases he : ∃ inp, tr[j]? = some (v, inp)
    · obtain ⟨inp, hj⟩ := he
      rw [step_before hj]
      refine step_keeps (by rw [← step_before hj]; exact reads_before hinj hbase hv _)
        (by rw [← step_before hj, base_before hbase hv, base_before hbase hv])
        (pend_before hinj hv j) (fun id b hib hid => ?_)
        (by
          rw [received_of_ne fun v1 B1 v2 B2 h => hnj j v v1 B1 v2 B2 hv (h ▸ hj)]
          exact fun e he => absurd he List.not_mem_nil)
        (fun h => hnr j v hv (h ▸ hj)) hf ih
      subst hib
      exact gT_of_known (x := (id, b)) hinj (Or.inl ⟨j, v, hj, hv, hid⟩)
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact ih

/-- **No pending block is ever ready.** -/
theorem noReady_before (v : Validator) : ∀ i, NoReady (stateBefore cfg tr i v)
  | 0 => fun e he => by simp [stateBefore, inputsBefore, run, State.init] at he
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [step_before hi]
      exact noReady_step (noReady_before v i) inp
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact noReady_before v i

/-- **A block becomes pending only by a delivery the node acts on.** -/
theorem entry_before (hnj : NoJump H tr) {v : Validator} (hv : v ∈ H)
    {y : BlockId × Block Validator BlockId Payload} {a : ℕ}
    (h₁ : y ∉ (stateBefore cfg tr a v).pending) (h₂ : y ∈ (stateBefore cfg tr (a + 1) v).pending) :
    tr[a]? = some (v, .deliver y.1 y.2) ∧ Admits (cfg.at v) (stateBefore cfg tr a v) y.1 y.2 := by
  by_cases he : ∃ inp, tr[a]? = some (v, inp)
  · obtain ⟨inp, ha⟩ := he
    rw [step_before ha] at h₂
    rcases (step_sub (cfg := cfg.at v) _ inp).1 y h₂ with h | ⟨rfl, hc⟩ | h
    · exact absurd h h₁
    · exact ⟨ha, hc⟩
    · rw [received_of_ne fun v1 B1 v2 B2 h => hnj a v v1 B1 v2 B2 hv (h ▸ ha)] at h
      exact absurd h List.not_mem_nil
  · rw [same_before fun inp h => he ⟨inp, h⟩] at h₂; exact absurd h₂ h₁

/-- **A request is recorded only on account of a delivery the node acted
on.** -/
theorem requested_before (v : Validator) : ∀ t, ∀ e ∈ (stateBefore cfg tr t v).requested,
    ∃ a < t, ∃ b, tr[a]? = some (v, .deliver e.2.1 b) ∧
      Admits (cfg.at v) (stateBefore cfg tr a v) e.2.1 b
  | 0, e, he => by simp [stateBefore, inputsBefore, run, State.init] at he
  | t + 1, e, he => by
    by_cases hev : ∃ inp, tr[t]? = some (v, inp)
    · obtain ⟨inp, ht⟩ := hev
      rw [step_before ht] at he
      rcases (step_sub (cfg := cfg.at v) _ inp).2 e he with he | ⟨b, rfl, hc⟩
      · obtain ⟨a, ha, b, hab, hc⟩ := requested_before v t e he
        exact ⟨a, by omega, b, hab, hc⟩
      · exact ⟨t, by omega, b, ht, hc⟩
    · rw [same_before fun inp h => hev ⟨inp, h⟩] at he
      obtain ⟨a, ha, b, hab, hc⟩ := requested_before v t e he
      exact ⟨a, by omega, b, hab, hc⟩

/-- **A delivery a node acts on keeps a fitting block it delivers.** -/
theorem admit_after (hinj : HashInjective cfg H tr)
    (hbase : ∀ v ∈ H, (stateBefore cfg tr tr.length v).store.base = 0)
    {v : Validator} (hv : v ∈ H) {a : ℕ} {id : BlockId} {b : Block Validator BlockId Payload}
    (ha : tr[a]? = some (v, .deliver id b)) (hc : Admits (cfg.at v) (stateBefore cfg tr a v) id b)
    (hf : Fits (cfg.at v) (gT cfg H tr) (id, b)) :
    (id, b) ∈ (stateBefore cfg tr (a + 1) v).pending ∨
      id ∈ (stateBefore cfg tr (a + 1) v).store.ids := by
  rw [step_before ha]
  exact admit_keeps hc (by rw [← step_before ha]; exact reads_before hinj hbase hv _)
    (by rw [← step_before ha, base_before hbase hv, base_before hbase hv])
    (pend_before hinj hv a) (gT_of_known (x := (id, b)) hinj (Or.inl ⟨a, v, ha, hv, hc.1⟩)) hf

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
  (hbase : ∀ v ∈ H, (stateBefore cfg tr tr.length v).store.base = 0)
include hinj hbase

omit hinj hbase in
theorem causal_store (i : ℕ) (v : Validator) :
    CausalStructure (stateBefore cfg tr i v).store.blk (stateBefore cfg tr i v).store.ids :=
  (stateBefore cfg tr i v).store.toRecord.causal

/-- **An honest store holding a block reads its history as the trace
does.** -/
theorem hist_eq {v : Validator} (hv : v ∈ H) {i : ℕ} {b : BlockId}
    (hb : b ∈ (stateBefore cfg tr i v).store.ids) :
    historyFrom (stateBefore cfg tr i v).store.blk b = historyFrom (gT cfg H tr) b :=
  historyFrom_congr (stateBefore cfg tr i v).store.complete (reads_before hinj hbase hv i).2 hb

theorem hist_sub {v : Validator} (hv : v ∈ H) {i : ℕ} {b : BlockId}
    (hb : b ∈ (stateBefore cfg tr i v).store.ids) :
    historyFrom (gT cfg H tr) b ⊆ (stateBefore cfg tr i v).store.ids := by
  rw [← hist_eq hinj hbase hv hb]
  exact (causal_store i v).history_subset_ids hb

omit hinj hbase in
/-- **What a node stores it knew.** -/
theorem stored_known {v : Validator} (hv : v ∈ H) {i : ℕ} {j : BlockId}
    (hj : j ∈ (stateBefore cfg tr i v).store.ids) :
    (j, (stateBefore cfg tr i v).store.map.getD j (stateBefore cfg tr i v).store.junk) ∈
      knownIn cfg H tr :=
  knownBefore_sub hv i ((inv_before (cfg := cfg) i v).known j hj)

/-- **A stored block fits every honest node.** -/
theorem fits_stored {u : Validator} (hu : u ∈ H) {i : ℕ} {j : BlockId}
    (hj : j ∈ (stateBefore cfg tr i u).store.ids) (v : Validator) :
    Fits (cfg.at v) (gT cfg H tr)
      (j, (stateBefore cfg tr i u).store.map.getD j (stateBefore cfg tr i u).store.junk) := by
  set st := (stateBefore cfg tr i u).store
  have hR := reads_before hinj hbase hu i
  refine fits_of_valid fun hr => ?_
  have hlt : st.base < (st.map.getD j st.junk).round := by rw [hR.1]; exact hr
  have hblk := Store.blk_of_lt hlt
  have href : ∀ k ∈ (st.map.getD j st.junk).refs, k ∈ st.ids := fun k hk =>
    st.complete j hj k (by change k ∈ (st.blk j).refs; rw [hblk]; exact hk)
  refine ⟨fun k hk => ?_, ?_⟩
  · have := st.pred j hj k (by change k ∈ (st.blk j).refs; rw [hblk]; exact hk)
    change (st.blk k).round + 1 = (st.blk j).round at this
    rw [hR.2 k (href k hk), hblk] at this
    exact this
  · refine rowValid_congr (fun k hk => ?_) ((inv_before (cfg := cfg) i u).valid j hj hlt)
    rw [hR.2 k (href k hk)]
    exact ⟨rfl, rfl⟩

omit hinj in
/-- **What an event makes its node stores after it.** -/
theorem persist_stored {i : ℕ} {u : Validator} {inp : Input Validator BlockId Payload}
    (hu : u ∈ H) (hi : tr[i]? = some (u, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) :
    e.1 ∈ (stateBefore cfg tr (i + 1) u).store.ids ∧
      (stateBefore cfg tr (i + 1) u).store.map.getD e.1
        (stateBefore cfg tr (i + 1) u).store.junk = e.2 := by
  rw [outputsAt_eq hi] at he
  rw [step_before hi]
  exact step_persist (by rw [← step_before hi, base_before hbase hu, base_before hbase hu]) e he

omit hinj hbase in
/-- **A block pending at the end entered once and stayed.** -/
theorem entry_time {v : Validator} {c : BlockId × Block Validator BlockId Payload}
    (hc : c ∈ (stateBefore cfg tr tr.length v).pending) :
    ∃ a < tr.length, c ∉ (stateBefore cfg tr a v).pending ∧
      ∀ t, a < t → t ≤ tr.length → c ∈ (stateBefore cfg tr t v).pending := by
  classical
  let Q : ℕ → Prop := fun x => ∀ t, x ≤ t → t ≤ tr.length → c ∈ (stateBefore cfg tr t v).pending
  have hQ : ∃ x, Q x := ⟨tr.length, fun t h₁ h₂ => by rw [show t = tr.length by omega]; exact hc⟩
  have hx0 : Nat.find hQ ≠ 0 := by
    intro h0
    have := Nat.find_spec hQ 0 (by omega) (Nat.zero_le _)
    simp [stateBefore, inputsBefore, run, State.init] at this
  have hxL : Nat.find hQ ≤ tr.length :=
    Nat.find_min' hQ fun t h₁ h₂ => by rw [show t = tr.length by omega]; exact hc
  refine ⟨Nat.find hQ - 1, by omega, ?_, fun t ht htL => Nat.find_spec hQ t (by omega) htL⟩
  intro hin
  have hmin := Nat.find_min hQ (show Nat.find hQ - 1 < Nat.find hQ by omega)
  apply hmin
  intro t ht htL
  rcases Nat.eq_or_lt_of_le ht with h | h
  · rw [← h]; exact hin
  · exact Nat.find_spec hQ t (by omega) htL

/-- **Below a pending block of an honest history, a chain of pending
blocks leads to a block the node lacks.** -/
theorem chain {u v : Validator} (hu : u ∈ H) (hv : v ∈ H) {τ : ℕ} {idh : BlockId}
    (hidh : idh ∈ (stateBefore cfg tr τ u).store.ids) (raw : BlockId → Block Validator BlockId Payload)
    (hraw : ∀ j, raw j = (stateBefore cfg tr τ u).store.map.getD j
      (stateBefore cfg tr τ u).store.junk) :
    ∀ n, ∀ w ∈ historyFrom (gT cfg H tr) idh, (raw w).round = n →
      (w, raw w) ∈ (stateBefore cfg tr tr.length v).pending →
      w ∉ (stateBefore cfg tr tr.length v).store.ids →
      ∃ (len : ℕ) (x : ℕ → BlockId), 0 < len ∧ x 0 = w ∧
        (∀ k ≤ len, x k ∈ historyFrom (gT cfg H tr) idh ∧
          x k ∉ (stateBefore cfg tr tr.length v).store.ids) ∧
        (∀ k < len, (x k, raw (x k)) ∈ (stateBefore cfg tr tr.length v).pending ∧
          x (k + 1) ∈ (raw (x k)).refs ∧ (raw (x (k + 1))).round + 1 = (raw (x k)).round) ∧
        x len ∉ (stateBefore cfg tr tr.length v).pending.map Prod.fst := by
  set st := (stateBefore cfg tr τ u).store with hst
  set fin := stateBefore cfg tr tr.length v with hfin
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hn hwp hws
  have hsub := hist_sub hinj hbase hu hidh
  have hwst : w ∈ st.ids := hsub hw
  have hnr := noReady_before (cfg := cfg) (tr := tr) v tr.length _ hwp
  simp only [ready, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hnr
  have hb0 := base_before hbase hv tr.length
  have hpos : 0 < (raw w).round := by
    have h1 := hnr.1
    change ¬ (raw w).round ≤ fin.store.base at h1
    rw [hb0] at h1; omega
  obtain ⟨r, hr, hrn⟩ := Finset.not_subset.mp hnr.2
  have hlt : st.base < (st.map.getD w st.junk).round := by
    rw [base_before hbase hu τ, ← hraw]; exact hpos
  have hblk : st.blk w = raw w := (Store.blk_of_lt hlt).trans (hraw w).symm
  have hrst : r ∈ st.ids :=
    st.complete w hwst r (by change r ∈ (st.blk w).refs; rw [hblk]; exact hr)
  have hrH : r ∈ historyFrom (gT cfg H tr) idh := by
    rw [← hist_eq hinj hbase hu hidh] at hw ⊢
    have C := causal_store (cfg := cfg) (tr := tr) τ u
    exact C.history_subset_of_reaches hidh ((C.mem_history_iff hidh).mp hw)
      (C.mem_history_of_mem_refs hwst (by rw [hblk]; exact hr))
  have hround : (raw r).round + 1 = (raw w).round := by
    have := st.pred w hwst r (by change r ∈ (st.blk w).refs; rw [hblk]; exact hr)
    change (st.blk r).round + 1 = (st.blk w).round at this
    rw [hblk] at this
    rw [hraw r]
    simpa [Store.blk, lookup] using this
  by_cases hrp : r ∈ fin.pending.map Prod.fst
  · obtain ⟨e, he, her⟩ := List.mem_map.mp hrp
    have hke : e.2 = raw r := by
      have h₁ := knownBefore_sub hv tr.length ((inv_before (cfg := cfg) tr.length v).pend e he)
      have h₂ := stored_known (cfg := cfg) (tr := tr) hu hrst
      rw [hraw]
      exact content_eq hinj h₁ h₂ her
    have hrp' : (r, raw r) ∈ fin.pending := by rw [← hke, ← her]; exact he
    obtain ⟨len, x, hlen, hx0, hxH, hxc, hxl⟩ := ih (raw r).round (by omega) r hrH rfl hrp' hrn
    refine ⟨len + 1, fun k => if k = 0 then w else x (k - 1), by omega, by simp, ?_, ?_, ?_⟩
    · intro k hk
      rcases k with _ | k
      · exact ⟨hw, hws⟩
      · simpa using hxH k (by omega)
    · intro k hk
      rcases k with _ | k
      · simp only [if_true, if_neg (Nat.succ_ne_zero 0), Nat.add_sub_cancel, hx0]
        exact ⟨hwp, hr, hround⟩
      · simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
        exact hxc k (by omega)
    · simpa using hxl
  · refine ⟨1, fun k => if k = 0 then w else r, Nat.one_pos, by simp, ?_, ?_, by simpa using hrp⟩
    · intro k hk
      rcases k with _ | k
      · exact ⟨hw, hws⟩
      · simp only [if_neg (Nat.succ_ne_zero _)]; exact ⟨hrH, hrn⟩
    · intro k hk
      rw [show k = 0 by omega]
      simp only [if_true, if_neg (Nat.succ_ne_zero 0)]
      exact ⟨hwp, hr, hround⟩

end Histories

end Converge

end Node

end LeanDag
