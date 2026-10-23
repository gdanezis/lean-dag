import LeanDag.Node.Helpers.Reliable
/-!
# Holding a history

`docs/validator.md` §5.2. A block stored or pending stays stored or
pending (`Stays`) from then on, since a pending block is accepted once
it is ready. A delivery of a block by its hash and of another author
leaves it stored or pending. A store with no pending block ready then
holds every block of a set closed under references, once each stays and
is ready when its references are accepted (`holds_of_stays`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **A block that stays**: stored or pending. -/
def Stays (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload))
    (y : BlockId × Block Validator BlockId Payload) : Prop :=
  y.1 ∈ st.ids ∨ y ∈ pend

/-! ## Agreeing with `g` -/

/-! ## Accepting a ready block -/

omit [Fintype Validator] in
/-- **`accept` takes a block when it is ready.** -/
theorem accept_takes {st : Store Validator BlockId Payload}
    {y : BlockId × Block Validator BlockId Payload} (hr : ready cfg st y = true) :
    y.1 ∈ (Node.accept cfg st y.1 y.2).ids := by
  unfold Node.accept
  by_cases hin : y.1 ∈ st.ids
  · split
    · exact Store.mem_insert_self
    · exact hin
  · simp only [ready, decide_eq_true_eq] at hr
    rw [dif_pos ⟨hin, hr.1, hr.2.1, hr.2.2⟩]
    exact Store.mem_insert_self

/-! ## Staying through a flush -/

omit [Fintype Validator] in
/-- **A fold of ready blocks takes each** of them. -/
theorem foldl_takes_under : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload} {y : BlockId × Block Validator BlockId Payload},
    ready cfg st y = true →
    (y ∈ l ∨ y.1 ∈ st.ids) → y.1 ∈ (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st).ids
  | [], _, _, _, h => by
    rcases h with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  | e :: l, st, y, hr, h => by
    simp only [List.foldl_cons]
    have hg := Grows.accept (cfg := cfg) st e.1 e.2
    refine foldl_takes_under l (ready_mono hg hr) ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (accept_takes hr)
      · exact Or.inl h
    · exact Or.inr (hg.1 h)

omit [Fintype Validator] in
/-- **A flush keeps a block stored or pending.** -/
theorem flush_stays : ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}
    {y : BlockId × Block Validator BlockId Payload},
    (y.1 ∈ st.ids ∨ y ∈ pend) →
    y.1 ∈ (Node.flush cfg fuel st pend).1.ids ∨ y ∈ (Node.flush cfg fuel st pend).2
  | 0, _, _, _, h => h
  | fuel + 1, st, pend, y, h => by
    unfold Node.flush
    dsimp only
    split
    · exact h
    · rw [List.partition_eq_filter_filter]
      set rd := pend.filter fun e => ready cfg st e
      have hg := Grows.foldl (cfg := cfg) rd st
      have hfold : y.1 ∈ (rd.foldl (fun s e => Node.accept cfg s e.1 e.2) st).ids ∨
          y ∈ pend.filter (not ∘ fun e => ready cfg st e) := by
        by_cases hry : ready cfg st y = true
        · left
          refine foldl_takes_under rd hry ?_
          rcases h with h | h
          · exact Or.inr h
          · exact Or.inl (List.mem_filter.mpr ⟨h, hry⟩)
        · rcases h with h | h
          · exact Or.inl (hg.1 h)
          · right
            refine List.mem_filter.mpr ⟨h, ?_⟩
            simp only [Function.comp_apply, Bool.not_eq_true'] at hry ⊢
            simp [hry]
      exact flush_stays fuel hfold

/-! ## Staying through a pass -/

omit [Fintype Validator] in
/-- **A pass keeps a block staying.** -/
theorem advance_stays {x : State Validator BlockId Payload}
    {y : BlockId × Block Validator BlockId Payload} (hst : Stays x.store x.pending y) :
    Stays (Node.advance cfg x).1.store (Node.advance cfg x).1.pending y := by
  simp only [Node.advance, Node.pass, arm_store, arm_pending, arm_top, arm_own, arm_fired, arm_lo,
      arm_decided]
  have hg₁ := (Grows.progress (cfg := cfg) (x.store.topRound + 2) x).1
  have hp₁ := progress_pending (cfg := cfg) (x.store.topRound + 2) x
  generalize Node.progress cfg (x.store.topRound + 2) x = r at hg₁ hp₁ ⊢
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := decideStep_pending (cfg := cfg) r.1
  refine flush_stays _ ?_
  rw [hd, hdp]
  rcases hst with h | h
  · exact Or.inl (hg₁.1 h)
  · exact Or.inr (hp₁ ▸ h)

omit [Fintype Validator] in
/-- **The passes keep a block staying.** -/
theorem quiesce_stays {y : BlockId × Block Validator BlockId Payload} :
    ∀ (n : ℕ) {x : State Validator BlockId Payload}, Stays x.store x.pending y →
    Stays (quiesce cfg n x).1.store (quiesce cfg n x).1.pending y
  | 0, _, hst => hst
  | n + 1, x, hst => by
    rcases quiesce_succ_cases (cfg := cfg) n x with he | he <;> rw [he]
    · exact advance_stays hst
    · exact quiesce_stays n (advance_stays hst)

omit [Fintype Validator] in
/-- **A settle keeps a block staying.** -/
theorem settle_stays {x : State Validator BlockId Payload}
    {y : BlockId × Block Validator BlockId Payload} (hst : Stays x.store x.pending y) :
    Stays (Node.settle cfg x).1.store (Node.settle cfg x).1.pending y :=
  quiesce_stays _ hst

/-! ## Staying through a step -/

/-- **A step keeps a block staying**; and a delivery of the block, by its
hash and of another author, with no other block pending under its
identifier, leaves it staying. -/
theorem step_stays {s : State Validator BlockId Payload}
    {inp : Input Validator BlockId Payload} {y : BlockId × Block Validator BlockId Payload}
    (hst : Stays s.store s.pending y ∨ (inp = .deliver y.1 y.2 ∧ y.1 = cfg.idOf y.2 ∧
      y.2.creator ≠ cfg.me ∧ ∀ e ∈ s.pending, e.1 = y.1 → e = y)) :
    Stays (Node.step cfg s inp).1.store (Node.step cfg s inp).1.pending y := by
  cases inp with
  | start =>
    have hst' : Stays s.store s.pending y := hst.elim id fun h => by cases h.1
    simp only [Node.step]
    split
    · split
      · apply settle_stays
        rcases hst' with h | h
        · exact Or.inl (by simp [Store.insert_ids, h])
        · exact Or.inr h
      · exact hst'
    · exact hst'
  | deliver j b =>
    by_cases hAd : Admits cfg s j b
    · rw [step_deliver hAd]
      apply settle_stays
      refine flush_stays _ ?_
      rcases hst with h | ⟨hinp, -, -, -⟩
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · injection hinp with h₁ h₂
        have hyb : y = (j, b) := Prod.ext h₁.symm h₂.symm
        exact Or.inr (hyb ▸ List.mem_cons_self)
    · rw [step_deliver_not hAd]
      rcases hst with hst | ⟨hinp, hid, hcr, huniq⟩
      · exact hst
      · injection hinp with h₁ h₂
        subst h₁ h₂
        by_cases hin : y.1 ∈ s.store.ids
        · exact Or.inl hin
        · by_cases hp : y.1 ∈ s.pending.map Prod.fst
          · obtain ⟨e, he, he1⟩ := List.mem_map.mp hp
            exact Or.inr (huniq e he he1 ▸ he)
          · exact absurd ⟨hid, hcr, hin, hp⟩ hAd
  | timer r => rw [step_timer_fst]; exact settle_stays (hst.elim id fun h => by cases h.1)
  | fetchRequest p r ids => exact hst.elim id fun h => by cases h.1
  | restart => exact hst.elim id fun h => by cases h.1

/-! ## Holding a closed set -/

omit [Fintype Validator] in
/-- **A store holds a set of blocks closed under references**, if each of
them stays, each is ready once its references are accepted, and no
pending block is ready. -/
theorem holds_of_stays {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}
    (hnr : ∀ e ∈ pend, ready cfg st e = false) {Z : Finset BlockId}
    (raw : BlockId → Block Validator BlockId Payload)
    (hst : ∀ z ∈ Z, Stays st pend (z, raw z))
    (hcl : ∀ z ∈ Z, ∀ r ∈ (raw z).refs, r ∈ Z ∧ (raw r).round + 1 = (raw z).round)
    (hrd : ∀ z ∈ Z, (raw z).refs ⊆ st.ids → ready cfg st (z, raw z) = true) :
    ∀ z ∈ Z, z ∈ st.ids := by
  suffices h : ∀ n z, z ∈ Z → (raw z).round = n → z ∈ st.ids from
    fun z hz => h _ z hz rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz hr
    rcases hst z hz with h | h
    · exact h
    · have hrefs : (raw z).refs ⊆ st.ids := fun r hr' => by
        obtain ⟨hrZ, hrr⟩ := hcl z hz r hr'
        exact ih _ (by omega) r hrZ rfl
      have := hnr _ h
      rw [hrd z hz hrefs] at this
      cases this

/-! ## Along a trace -/

variable {tr : Trace Validator BlockId Payload} {H : Finset Validator}

/-- **A step keeps a known block staying**, at an honest node; and a
delivery of it, of another author, leaves it staying. -/
theorem stays_succ (hinj : Converge.HashInjective cfg H tr)
    {v : Validator} (hv : v ∈ H)
    {y : BlockId × Block Validator BlockId Payload} (hyk : y ∈ Converge.knownIn cfg H tr)
    {a : ℕ}
    (hst : Stays (stateBefore cfg tr a v).store (stateBefore cfg tr a v).pending y ∨
      (tr[a]? = some (v, .deliver y.1 y.2) ∧ y.2.creator ≠ v)) :
    Stays (stateBefore cfg tr (a + 1) v).store (stateBefore cfg tr (a + 1) v).pending y := by
  rcases he : tr[a]? with _ | ⟨w, inp⟩
  · have hlen : tr.length ≤ a := List.getElem?_eq_none_iff.mp he
    have heq : stateBefore cfg tr (a + 1) v = stateBefore cfg tr a v := by
      unfold stateBefore
      rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ a + 1)]
    rw [heq]
    rcases hst with hst | ⟨h, -⟩
    · exact hst
    · rw [he] at h; cases h
  · rw [stateBefore_succ he]
    split
    · rename_i hw
      subst hw
      refine step_stays (cfg := cfg.at w) ?_
      rcases hst with hst | ⟨h, hcr⟩
      · exact Or.inl hst
      · have h₂ : inp = .deliver y.1 y.2 := by rw [he] at h; simpa using h
        refine Or.inr ⟨h₂, Converge.id_of_knownIn hyk, hcr, fun e he' he1 => ?_⟩
        have hek := Converge.knownBefore_sub hv a
          ((Converge.inv_before (cfg := cfg) a w).pend e he')
        exact Prod.ext he1 (Converge.content_eq hinj hek hyk he1)
    · rename_i hw
      rcases hst with hst | ⟨h, -⟩
      · exact hst
      · rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 hw

/-- **A known block stays from then on**, at an honest node, once it
stays. -/
theorem stays_from (hinj : Converge.HashInjective cfg H tr)
    {v : Validator} (hv : v ∈ H)
    {y : BlockId × Block Validator BlockId Payload} (hyk : y ∈ Converge.knownIn cfg H tr)
    {a : ℕ}
    (hst : Stays (stateBefore cfg tr a v).store (stateBefore cfg tr a v).pending y) :
    ∀ b, a ≤ b →
      Stays (stateBefore cfg tr b v).store (stateBefore cfg tr b v).pending y := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact hst
  | succ b hab ih => exact stays_succ hinj hv hyk (Or.inl ih)

end Node

end LeanDag
