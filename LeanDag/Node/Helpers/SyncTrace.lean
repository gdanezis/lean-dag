import LeanDag.Node.Helpers.SyncInv
import LeanDag.Node.Helpers.Arrive
/-!
# One sync along a trace

Along a trace a node's syncs keep their shape and only evidence convicts
an author (`syncsOn_before`, `evidenceOn_before`), so an honest node
never convicts an honest one, given authentic evidence (`not_detected`).
A sync present at `τ` was asked for last at some event `R < τ`, and has
been present since, asking only for names of that request (`last_ask`).

For an honest node `u` whose own blocks lie at or below the round of its
block `(j, b)`, a node `v` that never holds `j` and is given `(j, b)` by
`u` has a sync for it from then on (`sync_made`, `sync_stays`).
-/

namespace LeanDag

namespace Node

namespace Converge

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

/-- **What a node made is on its disk.** -/
theorem own_stored {w : Validator} {E : ℕ} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ persists (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr E w)).2) :
    x.1 ∈ (stateBefore cfg tr E w).disk.ids ∧ (stateBefore cfg tr E w).disk.blk x.1 = x.2 := by
  obtain ⟨j, hjE, hjw, hxj⟩ := mem_persists_before (cfg := cfg) w E hx
  obtain ⟨inp, hj⟩ := event_of_map hjw
  obtain ⟨h₁, h₂⟩ := persist_stored hj hxj
  have hg := grows_before (cfg := cfg) (tr := tr) w (show j + 1 ≤ E by omega)
  exact ⟨hg.1 h₁, by rw [hg.blk h₁]; exact h₂⟩

/-- **What a node made by an event it made by the end.** -/
theorem persists_final {w : Validator} {E : ℕ} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ persists (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr E w)).2) :
    x ∈ persists (runOf cfg tr w).2 := by
  rcases le_total E tr.length with h | h
  · exact persists_before_mono w h x hx
  · unfold runOf; rwa [inputsBefore_of_le h] at hx

/-- **A block an honest node is given with an honest author's identity**
its author made. -/
theorem auth_final (htime : TimelyAuthentic cfg H tr) {u v : Validator} (hu : u ∈ H)
    (hv : v ∈ H) {τ : ℕ} {inp : Input Validator BlockId Payload} (hτ : tr[τ]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ delivered (cfg.at v) [inp])
    (hc : x.2.creator = u) : x ∈ persists (runOf cfg tr u).2 := by
  obtain ⟨p, -, hpu, hpb⟩ := htime τ v inp hτ hv x hx (by rw [hc]; exact hu)
  rw [hc] at hpu
  obtain ⟨inpp, hp⟩ := event_of_map hpu
  obtain ⟨i, -, inpi, hi, hix⟩ := persists_of_broadcasts hp hpb
  exact persists_final (persists_of_event hi hix)

/-- **An honest node never convicts an honest one.** -/
theorem not_detected (htime : TimelyAuthentic cfg H tr) (hev : EvidenceAuthentic cfg H tr)
    {u v : Validator} (hu : u ∈ H) (hv : v ∈ H) (i : ℕ) :
    u ∉ (stateBefore cfg tr i v).detected := by
  wlog hi : i ≤ tr.length generalizing i
  · rw [stateBefore_of_le (by omega) v]; exact this tr.length le_rfl
  intro hd
  have hE := evidenceOn_before (cfg := cfg) (tr := tr) v i
  obtain ⟨e, he, rfl, hne⟩ := hE.1 _ hd
  rcases (hE.2 e he).2 with ⟨ha, ha', hac, hac', hr⟩ | ⟨c, hc, hce⟩
  · have hown : ∀ c ∈ (stateBefore cfg tr i v).disk.ids,
        ((stateBefore cfg tr i v).disk.blk c).creator = e.1 →
        (c, (stateBefore cfg tr i v).disk.blk c) ∈ persists (runOf cfg tr e.1).2 := fun c hc hcu =>
      persists_final (own_known (v := e.1) htime hv hu hi ((inv_before i v).known c hc) hcu)
    exact hne (Prod.mk.inj (eq_of_persists e.1 (hown _ ha hac) (hown _ ha' hac') hr)).1
  · exact hev _ (stored_known hv hc) e hce hne hu

/-- **An honest node leaves out no honest author**, given authentic
evidence. -/
theorem not_excluded (htime : TimelyAuthentic cfg H tr) (hev : EvidenceAuthentic cfg H tr)
    {u v : Validator} (hu : u ∈ H) (hv : v ∈ H) (i r : ℕ) :
    u ∉ excluded (cfg.at v) (stateBefore cfg tr i v).disk r (stateBefore cfg tr i v).evidence := by
  wlog hi : i ≤ tr.length generalizing i
  · rw [stateBefore_of_le (by omega) v]; exact this tr.length le_rfl
  have hE := evidenceOn_before (cfg := cfg) (tr := tr) v i
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨he, hne⟩ := Finset.mem_filter.mp he
    rcases (hE.2 e he).2 with ⟨ha, ha', hac, hac', hr⟩ | ⟨c, hc, hce⟩
    · have hown : ∀ c ∈ (stateBefore cfg tr i v).disk.ids,
          ((stateBefore cfg tr i v).disk.blk c).creator = e.1 →
          (c, (stateBefore cfg tr i v).disk.blk c) ∈ persists (runOf cfg tr e.1).2 :=
        fun c hc hcu =>
          persists_final (own_known (v := e.1) htime hv hu hi ((inv_before i v).known c hc) hcu)
      exact hne (Prod.mk.inj (eq_of_persists e.1 (hown _ ha hac) (hown _ ha' hac') hr)).1
    · exact hev _ (stored_known hv hc) e hce hne hu
  · obtain ⟨c, hcR, hcm⟩ := Finset.mem_biUnion.mp hm
    exact ex_not_named (inv_before (cfg := cfg) (tr := tr) i v).valid
      (fun j hj e he hne => hev _ (stored_known hv hj) e he hne) c
      (Store.mem_atRound.mp hcR).1 u hcm hu

/-- **The last request of a sync**: a sync present at `τ` was asked for
at an event `R < τ` with no later request for it before `τ`, and has been
present since, asking only for names of that request. -/
theorem last_ask {v w : Validator} {t : BlockId × Block Validator BlockId Payload} :
    ∀ τ, (∃ A, (w, t, A) ∈ (stateBefore cfg tr τ v).syncs) →
      ∃ R < τ, ∃ fr ids, (∃ inp, tr[R]? = some (v, inp)) ∧
        Output.sync w t.1 fr ids ∈ outputsAt cfg tr R ∧
        (∀ R', R < R' → R' < τ → ∀ inp, tr[R']? = some (v, inp) →
          ∀ fr' ids', Output.sync w t.1 fr' ids' ∉ outputsAt cfg tr R') ∧
        ∀ τ', R < τ' → τ' ≤ τ →
          ∃ A, (w, t, A) ∈ (stateBefore cfg tr τ' v).syncs ∧ ∀ x ∈ A, x ∈ ids
  | 0, ⟨A, hA⟩ => by simp [stateBefore, inputsBefore, run, State.init] at hA
  | τ + 1, ⟨A', hA'⟩ => by
    by_cases hev : ∃ inp, tr[τ]? = some (v, inp)
    · obtain ⟨inp, hτ⟩ := hev
      have hs := syncsOn_before (cfg := cfg) (tr := tr) v τ
      rw [step_before hτ] at hA'
      have hout := outputsAt_eq (cfg := cfg) hτ
      by_cases hreq : ∃ fr ids, Output.sync w t.1 fr ids ∈
          (Node.step (cfg.at v) (stateBefore cfg tr τ v) inp).2
      · obtain ⟨fr, ids, hmem⟩ := hreq
        refine ⟨τ, by omega, fr, ids, ⟨inp, hτ⟩, by rw [hout]; exact hmem,
          fun R' h₁ h₂ => absurd h₂ (by omega), fun τ' h₁ h₂ => ?_⟩
        obtain rfl : τ' = τ + 1 := by omega
        rw [step_before hτ]
        exact ⟨A', hA', by rw [step_ask hs hA' hmem]; exact fun x hx => hx⟩
      · push Not at hreq
        rcases step_origin hs hA' with ⟨fr, ids, h⟩ | ⟨A, hA⟩
        · exact absurd h (hreq fr ids)
        obtain ⟨R, hR, fr, ids, hev, hmem, hno, hall⟩ := last_ask τ ⟨A, hA⟩
        refine ⟨R, by omega, fr, ids, hev, hmem, fun R' h₁ h₂ inp' hR' => ?_,
          fun τ' h₁ h₂ => ?_⟩
        · rcases Nat.lt_or_ge R' τ with h | h
          · exact hno R' h₁ h inp' hR'
          · obtain rfl : R' = τ := by omega
            rw [hτ] at hR'
            obtain rfl : inp = inp' := (Prod.mk.inj (Option.some.inj hR')).2
            rw [hout]; exact hreq
        · rcases Nat.lt_or_ge τ' (τ + 1) with h | h
          · exact hall τ' h₁ (by omega)
          · obtain rfl : τ' = τ + 1 := by omega
            obtain ⟨A₀, hA₀, hsub⟩ := hall τ hR le_rfl
            rw [step_before hτ]
            exact ⟨A', hA', fun x hx => hsub x (step_same hs hA₀ hA' hreq x hx)⟩
    · have hsame := same_before (cfg := cfg) (tr := tr) (v := v) fun inp h => hev ⟨inp, h⟩
      rw [hsame] at hA'
      obtain ⟨R, hR, fr, ids, hevR, hmem, hno, hall⟩ := last_ask τ ⟨A', hA'⟩
      refine ⟨R, by omega, fr, ids, hevR, hmem, fun R' h₁ h₂ inp hR' => ?_, fun τ' h₁ h₂ => ?_⟩
      · rcases Nat.lt_or_ge R' τ with h | h
        · exact hno R' h₁ h inp hR'
        · obtain rfl : R' = τ := by omega
          exact absurd ⟨inp, hR'⟩ hev
      · rcases Nat.lt_or_ge τ' (τ + 1) with h | h
        · exact hall τ' h₁ (by omega)
        · obtain rfl : τ' = τ + 1 := by omega
          rw [hsame]; exact hall τ hR le_rfl

omit [Fintype Validator] in
/-- **A block ready and new is accepted.** -/
theorem mem_accept {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hr : ready cfg s (id, b) = true)
    (hn : id ∉ s.disk.ids) : id ∈ (Node.accept cfg s id b).disk.ids := by
  rw [accept_disk]
  rw [ready_eq] at hr
  simp only [readyOn, decide_eq_true_eq] at hr
  unfold acceptOn
  rw [dif_pos ⟨hn, hr⟩]
  exact Store.mem_insert_self

section Top

variable (htime : TimelyAuthentic cfg H tr) (hev : EvidenceAuthentic cfg H tr)
variable {u v : Validator} (hu : u ∈ H) (hv : v ∈ H) (huv : u ≠ v) {j : BlockId}
  {b : Block Validator BlockId Payload}
variable (hpers : (j, b) ∈ persists (runOf cfg tr u).2)
variable (htop : ∀ x ∈ persists (runOf cfg tr u).2, x.2.round ≤ b.round)
variable (hlack : ∀ τ, j ∉ (stateBefore cfg tr τ v).disk.ids)

include hpers htop in
/-- **A block of `u`'s at the round of `(j, b)` or above is `(j, b)`.** -/
theorem eq_top {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ persists (runOf cfg tr u).2) (hr : b.round ≤ x.2.round) : x = (j, b) :=
  eq_of_persists u hx hpers (le_antisymm (htop x hx) hr)

include htime hev hu hv huv hpers htop hlack in
/-- **`v` given `(j, b)` by `u` has a sync for it after.** -/
theorem sync_made (hid : j = cfg.idOf b) (hc : b.creator = u)
    (hval : 0 < b.round → cfg.q ≤ b.refs.card) {k : ℕ}
    (hk : tr[k]? = some (v, .deliver u j b)) :
    ∃ A, (u, (j, b), A) ∈ (stateBefore cfg tr (k + 1) v).syncs := by
  have hs := syncsOn_before (cfg := cfg) (tr := tr) v k
  have hl := hlack (k + 1)
  have hd := not_detected htime hev hu hv (k + 1)
  rw [step_before hk] at hl hd ⊢
  set s := stateBefore cfg tr k v
  have hg : j = (cfg.at v).idOf b ∧ b.creator = u ∧ u ≠ (cfg.at v).me ∧ u ∉ s.detected ∧
      j ∉ s.disk.ids := ⟨hid, hc, huv, not_detected htime hev hu hv k, hlack k⟩
  rw [step_deliver_eq, if_pos hg] at hl hd ⊢
  split_ifs at hl hd ⊢ with hr hcnd
  · exact absurd ((Thins.settle _).grows.1 ((Thins.tidy (cfg := cfg.at v) _).grows.1 (mem_accept hr
      hg.2.2.2.2))) hl
  · rcases (Thins.settle (cfg := cfg.at v) { s with syncs := (u, (j, b), ([] : List BlockId)) ::
        (s.syncs.filter fun e => decide (e.1 ≠ u)) }).kept _ List.mem_cons_self with h | h | h
    · exact ⟨[], h⟩
    · exact absurd h hl
    · exact absurd h hd
  · have hall : ¬ ((s.syncs.find? fun e => decide (e.1 = u)).all
        fun e => decide (e.2.1.2.round < b.round)) = true := fun h => hcnd ⟨hval, h⟩
    cases hf : s.syncs.find? fun e => decide (e.1 = u) with
    | none => rw [hf] at hall; exact absurd rfl hall
    | some e =>
      rw [hf] at hall
      simp only [Option.all_some, decide_eq_true_eq, not_lt] at hall
      have he := List.mem_of_find?_eq_some hf
      have heu : e.1 = u := by simpa using List.find?_some hf
      have hec : e.2.1.2.creator = u := (hs.2 e he).2.trans heu
      have hfin := persists_final (own_known (v := u) htime hv hu (le_refl k)
        ((inv_before k v).pend e he) hec)
      have := eq_top hpers htop (persists_final (persists_before_mono u
        (le_refl _) _ hfin)) hall
      refine ⟨e.2.2, ?_⟩
      obtain ⟨e₁, e₂, e₃⟩ := e
      simp only at heu this
      subst heu this
      exact he

include htime hev hu hv htop hlack in
/-- **`v`'s sync for `(j, b)` stays.** -/
theorem sync_stays {k : ℕ} (hmade : ∃ A, (u, (j, b), A) ∈ (stateBefore cfg tr (k + 1) v).syncs) :
    ∀ τ, k + 1 ≤ τ → ∃ A, (u, (j, b), A) ∈ (stateBefore cfg tr τ v).syncs := by
  intro τ hτ
  induction τ, hτ using Nat.le_induction with
  | base => exact hmade
  | succ τ _ ih =>
    obtain ⟨A, hA⟩ := ih
    by_cases hev : ∃ inp, tr[τ]? = some (v, inp)
    · obtain ⟨inp, hτ⟩ := hev
      have hl := hlack (τ + 1)
      have hd := not_detected htime hev hu hv (τ + 1)
      rw [step_before hτ] at hl hd ⊢
      rcases step_keeps (syncsOn_before (cfg := cfg) (tr := tr) v τ) hA inp with
        h | h | ⟨id, b', rfl, hid', hc', hr'⟩ | h
      · exact absurd h hl
      · exact absurd h hd
      · have hx : (id, b') ∈ delivered (cfg.at v) [Input.deliver u id b'] := by
          simp [delivered, hid']
        have : b'.round ≤ b.round := htop _ (auth_final htime hu hv hτ hx hc')
        change b.round < b'.round at hr'
        omega
      · exact h
    · rw [same_before fun inp h => hev ⟨inp, h⟩]; exact ⟨A, hA⟩

end Top

end Converge

end Node

end LeanDag
