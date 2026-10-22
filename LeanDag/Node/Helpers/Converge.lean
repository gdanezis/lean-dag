import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.Trace
import LeanDag.Node.Helpers.Walk
import LeanDag.Node.Helpers.Global
/-!
# The honest nodes along a trace

The blocks honest nodes knew over a trace give one block map (`gT`); an
honest node's store reads as it at every event (`reads_before`). Over
time then: a block that fits stays pending or stored (`keeps_after`); no
pending block is ever ready (`noReady_before`); a block becomes pending
only by a delivery the node acts on (`entry_before`); and a request is
recorded only on account of such a delivery (`requested_before`). Below
a pending block of an honest history, a chain of pending blocks leads to
a block the node lacks (`chain`).
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

theorem knownBefore_sub {v : Validator} (hv : v ∈ H) (i : ℕ) :
    knownBefore cfg tr i v ⊆ knownIn cfg H tr := by
  intro x hx
  simp only [knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨j, -, inp, hj, hd⟩ := mem_delivered_before (cfg.at v) v i hx
    exact Or.inl ⟨j, v, inp, hj, hv, hd⟩
  · obtain ⟨j, -, hjv, hx⟩ := mem_persists_before (cfg := cfg) v i hx
    exact Or.inr ⟨j, v, hjv, hv, hx⟩

/-- **What an event broadcasts it made.** -/
theorem persists_of_broadcasts {i : ℕ} {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ broadcasts (outputsAt cfg tr i)) : e ∈ persists (outputsAt cfg tr i) := by
  unfold outputsAt at he ⊢
  split at he
  · rename_i v inp _
    obtain ⟨bs, ho, -⟩ := (inv_before (cfg := cfg) (tr := tr) i v).step inp
    rw [ho.2] at he
    rw [ho.1]
    exact he
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

omit [Fintype Validator] in
/-- **A block an honest node knew from an input** was delivered to it. -/
theorem deliver_of_delivered {j : ℕ} {v : Validator}
    {inp : Input Validator BlockId Payload} (hj : tr[j]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ delivered (cfg.at v) [inp]) :
    tr[j]? = some (v, .deliver x.1 x.2) ∧ x.1 = cfg.idOf x.2 := by
  have hid := id_of_delivered hx
  cases inp with
  | deliver id b =>
    simp only [delivered, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    split at hx
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨hj, hid⟩
    · exact absurd hx List.not_mem_nil
  | _ => simp [delivered] at hx

theorem stateBefore_of_le {i : ℕ} (h : tr.length ≤ i) (v : Validator) :
    stateBefore cfg tr i v = stateBefore cfg tr tr.length v := by
  unfold stateBefore; rw [inputsBefore_of_le h]

/-- **Every honest store reads as the trace's block map.** -/
theorem reads_before (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) (i : ℕ) :
    ReadsAs (gT cfg H tr) (stateBefore cfg tr i v).store := fun j hj =>
  (gT_of_known hinj (knownBefore_sub hv i ((inv_before (cfg := cfg) i v).known j hj))).symm

theorem pend_before (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) (i : ℕ) :
    ∀ e ∈ (stateBefore cfg tr i v).pending, gT cfg H tr e.1 = e.2 := fun e he =>
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
theorem keeps_after (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H)
    {y : BlockId × Block Validator BlockId Payload}
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
      refine step_keeps (by rw [← step_before hj]; exact reads_before hinj hv _)
        (pend_before hinj hv j) (fun id b hib hid => ?_) hf ih
      subst hib
      exact gT_of_known (x := (id, b)) hinj
        (Or.inl ⟨j, v, .deliver id b, hj, hv, by simp [delivered, ← hid]⟩)
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact ih

/-- **No pending block is ever ready.** -/
theorem noReady_before (v : Validator) : ∀ i, NoReady (cfg.at v) (stateBefore cfg tr i v)
  | 0 => fun e he => by simp [stateBefore, inputsBefore, run, State.init] at he
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [step_before hi]
      exact noReady_step (cfg := cfg.at v) (noReady_before v i) inp
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact noReady_before v i

/-- **A block becomes pending only by a delivery the node acts on.** -/
theorem entry_before {v : Validator}
    {y : BlockId × Block Validator BlockId Payload} {a : ℕ}
    (h₁ : y ∉ (stateBefore cfg tr a v).pending) (h₂ : y ∈ (stateBefore cfg tr (a + 1) v).pending) :
    tr[a]? = some (v, .deliver y.1 y.2) ∧ Admits (cfg.at v) (stateBefore cfg tr a v) y.1 y.2 := by
  by_cases he : ∃ inp, tr[a]? = some (v, inp)
  · obtain ⟨inp, ha⟩ := he
    rw [step_before ha] at h₂
    rcases (step_sub (cfg := cfg.at v) _ inp).1 y h₂ with h | ⟨rfl, hc⟩
    · exact absurd h h₁
    · exact ⟨ha, hc⟩
  · rw [same_before fun inp h => he ⟨inp, h⟩] at h₂; exact absurd h₂ h₁

/-- **A request is recorded only on account of a delivery the node acted
on.** -/
theorem requested_before (v : Validator) : ∀ t, ∀ e ∈ (stateBefore cfg tr t v).requested,
    ∃ a < t, ∃ b, tr[a]? = some (v, .deliver e.2 b) ∧
      Admits (cfg.at v) (stateBefore cfg tr a v) e.2 b
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
theorem admit_after (hinj : HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) {a : ℕ}
    {id : BlockId} {b : Block Validator BlockId Payload}
    (ha : tr[a]? = some (v, .deliver id b)) (hc : Admits (cfg.at v) (stateBefore cfg tr a v) id b)
    (hf : Fits (cfg.at v) (gT cfg H tr) (id, b)) :
    (id, b) ∈ (stateBefore cfg tr (a + 1) v).pending ∨
      id ∈ (stateBefore cfg tr (a + 1) v).store.ids := by
  rw [step_before ha]
  exact admit_keeps hc (by rw [← step_before ha]; exact reads_before hinj hv _)
    (pend_before hinj hv a) (gT_of_known (x := (id, b)) hinj
      (Or.inl ⟨a, v, .deliver id b, ha, hv, by simp [delivered, ← hc.1]⟩)) hf

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
    CausalStructure (stateBefore cfg tr i v).store.blk (stateBefore cfg tr i v).store.ids :=
  (stateBefore cfg tr i v).store.toRecord.causal

/-- **An honest store holding a block reads its history as the trace
does.** -/
theorem hist_eq {v : Validator} (hv : v ∈ H) {i : ℕ} {b : BlockId}
    (hb : b ∈ (stateBefore cfg tr i v).store.ids) :
    historyFrom (stateBefore cfg tr i v).store.blk b = historyFrom (gT cfg H tr) b :=
  historyFrom_congr (stateBefore cfg tr i v).store.complete (reads_before hinj hv i) hb

theorem hist_sub {v : Validator} (hv : v ∈ H) {i : ℕ} {b : BlockId}
    (hb : b ∈ (stateBefore cfg tr i v).store.ids) :
    historyFrom (gT cfg H tr) b ⊆ (stateBefore cfg tr i v).store.ids := by
  rw [← hist_eq hinj hv hb]
  exact (causal_store i v).history_subset_ids hb

omit hinj in
/-- **What a node stores it knew.** -/
theorem stored_known {v : Validator} (hv : v ∈ H) {i : ℕ} {j : BlockId}
    (hj : j ∈ (stateBefore cfg tr i v).store.ids) :
    (j, (stateBefore cfg tr i v).store.blk j) ∈ knownIn cfg H tr :=
  knownBefore_sub hv i ((inv_before (cfg := cfg) i v).known j hj)

/-- **A stored block fits every honest node.** -/
theorem fits_stored {u : Validator} (hu : u ∈ H) {i : ℕ} {j : BlockId}
    (hj : j ∈ (stateBefore cfg tr i u).store.ids) (v : Validator) :
    Fits (cfg.at v) (gT cfg H tr) (j, (stateBefore cfg tr i u).store.blk j) := by
  set st := (stateBefore cfg tr i u).store
  have hR := reads_before hinj hu i
  have href : ∀ k ∈ (st.blk j).refs, k ∈ st.ids := st.complete j hj
  refine fits_of_valid ⟨fun k hk => ?_, ?_⟩
  · rw [← hR k (href k hk)]
    exact st.pred j hj k hk
  · refine rowValid_congr (fun k hk => ?_) ((inv_before (cfg := cfg) i u).valid j hj)
    rw [hR k (href k hk)]
    exact ⟨rfl, rfl⟩

omit hinj in
/-- **What an event makes its node stores after it.** -/
theorem persist_stored {i : ℕ} {u : Validator} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (u, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) :
    e.1 ∈ (stateBefore cfg tr (i + 1) u).store.ids ∧
      (stateBefore cfg tr (i + 1) u).store.blk e.1 = e.2 := by
  rw [outputsAt_eq hi] at he
  rw [step_before hi]
  exact step_persist e he

omit hinj in
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
    (hidh : idh ∈ (stateBefore cfg tr τ u).store.ids)
    (raw : BlockId → Block Validator BlockId Payload)
    (hraw : ∀ j, raw j = (stateBefore cfg tr τ u).store.blk j) :
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
  have hsub := hist_sub hinj hu hidh
  have hwst : w ∈ st.ids := hsub hw
  have hnr := noReady_before (cfg := cfg) (tr := tr) v tr.length _ hwp
  simp only [ready, decide_eq_false_iff_not] at hnr
  have hblk : st.blk w = raw w := (hraw w).symm
  -- the block is valid as `u` stored it, so it waits only for references
  have hpredw : ∀ j ∈ (raw w).refs, (st.blk j).round + 1 = (raw w).round := fun j hj => by
    rw [← hblk]; exact st.pred w hwst j (by rw [← hblk] at hj; exact hj)
  have hagree : ∀ j ∈ (raw w).refs, j ∈ fin.store.ids → fin.store.blk j = st.blk j := by
    intro j hj hjf
    have hjst : j ∈ st.ids := st.complete w hwst j (by rw [← hblk] at hj; exact hj)
    exact content_eq hinj (stored_known (cfg := cfg) (tr := tr) hv hjf)
      (stored_known (cfg := cfg) (tr := tr) hu hjst) rfl
  have hval : rowValid cfg.q st.blk (raw w) := by
    rw [← hblk]; exact (inv_before (cfg := cfg) τ u).valid w hwst
  have hns : ¬ (raw w).refs ⊆ fin.store.ids := by
    intro hsub'
    refine hnr ⟨hsub', fun j hj => ?_, rowValid_congr (fun j hj => ?_) hval⟩
    · rw [hagree j hj (hsub' hj)]; exact hpredw j hj
    · have hjw : j ≠ w := by
        intro h; subst h
        have := hpredw j hj
        rw [hblk] at this
        omega
      rw [Function.update_of_ne hjw, hagree j hj (hsub' hj)]
      exact ⟨rfl, rfl⟩
  obtain ⟨r, hr, hrn⟩ := Finset.not_subset.mp hns
  have hrst : r ∈ st.ids := st.complete w hwst r (by rw [← hblk] at hr; exact hr)
  have hrH : r ∈ historyFrom (gT cfg H tr) idh := by
    rw [← hist_eq hinj hu hidh] at hw ⊢
    have C := causal_store (cfg := cfg) (tr := tr) τ u
    exact C.history_subset_of_reaches hidh ((C.mem_history_iff hidh).mp hw)
      (C.mem_history_of_mem_refs hwst (by rw [hblk]; exact hr))
  have hround : (raw r).round + 1 = (raw w).round := by
    rw [hraw r]; exact hpredw r hr
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
