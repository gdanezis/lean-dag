import LeanDag.Node.Helpers.Steps
/-!
# Rate limiting bounds the store — the lemmas

`docs/validator.md` §3.9, V10. With a budget `τ` and a window `W`, every
block the node holds is charged to a slot at or above its round
(`Charged`), every slot charged lies between the horizon and `W` above
the top, and each slot is charged at most `τ + 1` blocks, at most `τ`
above the top (`Lim`). Every step keeps this (`Lim.step`), so the charges,
and with them the blocks held, number at most `n·(τ + 1)` a round of the
window (`length_le_of_slots`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **A block charged in `O`**: some charge names its identifier, at a slot
no lower than its round. -/
def Charged (O : List (BlockId × (Validator × ℕ))) (x : BlockId × Block Validator BlockId Payload) :
    Prop :=
  ∃ e ∈ O, e.1 = x.1 ∧ x.2.round ≤ e.2.2

/-- **The storage invariant** at a budget `τ` and a window `W`. -/
structure Lim (τ W : ℕ) (s : State Validator BlockId Payload) : Prop where
  store : ∀ j ∈ s.store.ids, Charged s.owner (j, s.store.map.getD j s.store.junk)
  pend : ∀ e ∈ s.pending, Charged s.owner e
  slots : ∀ e ∈ s.owner, s.store.base ≤ e.2.2 ∧ e.2.2 ≤ s.top.getD 0 + W
  charge : ∀ sl, s.charge sl ≤ τ + 1
  fresh : ∀ sl, (∀ t ∈ s.top, t < sl.2) → s.charge sl ≤ τ
  base : s.store.base ≤ s.top.getD 0

/-! ## Counting -/

omit [LinearOrder BlockId] in
/-- **The count**: charges at slots between `a` and `c`, at most `τ` a
slot, number at most `n·τ·(c + 1 − a)`. -/
theorem length_le_of_slots {O : List (BlockId × (Validator × ℕ))} {a c τ : ℕ}
    (hs : ∀ e ∈ O, a ≤ e.2.2 ∧ e.2.2 ≤ c)
    (hc : ∀ sl, (O.filter fun e => decide (e.2 = sl)).length ≤ τ) :
    O.length ≤ Fintype.card Validator * τ * (c + 1 - a) := by
  let S : Finset (Validator × ℕ) := Finset.univ ×ˢ Finset.Icc a c
  have hS : S.card = Fintype.card Validator * (c + 1 - a) := by
    simp [S, Finset.card_product, Nat.card_Icc]
  let m : Multiset (Validator × ℕ) := (O.map Prod.snd : Multiset (Validator × ℕ))
  have hm : Multiset.card m = O.length := by simp [m]
  have hsub : m.toFinset ⊆ S := by
    intro x hx
    simp only [m, Multiset.mem_toFinset, Multiset.mem_coe, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simpa [S] using hs e he
  have hcount : ∀ x, m.count x ≤ τ := by
    intro x
    refine le_trans (le_of_eq ?_) (hc x)
    rw [Multiset.count_eq_card_filter_eq]
    simp only [m, Multiset.filter_coe, Multiset.coe_card, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro e _
    simp [eq_comm]
  calc O.length = Multiset.card m := hm.symm
    _ = ∑ x ∈ m.toFinset, m.count x := (Multiset.toFinset_sum_count_eq m).symm
    _ ≤ ∑ x ∈ S, m.count x := Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ _x ∈ S, τ := Finset.sum_le_sum fun x _ => hcount x
    _ = Fintype.card Validator * τ * (c + 1 - a) := by
      rw [Finset.sum_const, hS, smul_eq_mul, Nat.mul_right_comm]

omit [Fintype Validator] in
/-- The blocks held are among the identifiers charged. -/
theorem held_subset {τ W : ℕ} {s : State Validator BlockId Payload} (h : Lim τ W s) :
    s.store.ids ∪ (s.pending.map Prod.fst).toFinset ⊆ (s.owner.map Prod.fst).toFinset := by
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · obtain ⟨e, he, hej, -⟩ := h.store j hj
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, hej⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    obtain ⟨e, he, hej, -⟩ := h.pend x hx
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, hej⟩)

/-- **The storage bound** of a state the invariant holds of: the charges,
and the blocks held, number at most `n·(τ + 1)` a round from the horizon
to `W` above the top. -/
theorem Lim.bound {τ W : ℕ} {s : State Validator BlockId Payload} (h : Lim τ W s) :
    (s.store.ids ∪ (s.pending.map Prod.fst).toFinset).card ≤ s.owner.length ∧
      s.owner.length ≤
        Fintype.card Validator * (τ + 1) * (s.top.getD 0 + W + 1 - s.store.base) := by
  refine ⟨(Finset.card_le_card (held_subset h)).trans ?_, length_le_of_slots h.slots h.charge⟩
  exact (List.toFinset_card_le _).trans (by rw [List.length_map])

/-! ## Charges -/

omit [Fintype Validator] [LinearOrder BlockId] in
theorem charge_append (l O : List (BlockId × (Validator × ℕ))) (sl : Validator × ℕ) :
    ((l ++ O).filter fun e => decide (e.2 = sl)).length =
      (l.filter fun e => decide (e.2 = sl)).length +
        (O.filter fun e => decide (e.2 = sl)).length := by
  rw [List.filter_append, List.length_append]

omit [Fintype Validator] [LinearOrder BlockId] in
theorem charge_filter_le (O : List (BlockId × (Validator × ℕ)))
    (p : BlockId × (Validator × ℕ) → Bool)
    (sl : Validator × ℕ) :
    ((O.filter p).filter fun e => decide (e.2 = sl)).length ≤
      (O.filter fun e => decide (e.2 = sl)).length :=
  ((List.filter_sublist (l := O) (p := p)).filter _).length_le

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem charged_mono {O O' : List (BlockId × (Validator × ℕ))} (h : ∀ e ∈ O, e ∈ O')
    {x : BlockId × Block Validator BlockId Payload} (hx : Charged O x) : Charged O' x := by
  obtain ⟨e, he, h₁, h₂⟩ := hx
  exact ⟨e, h e he, h₁, h₂⟩

omit [Fintype Validator] in
/-- The charges of one block of the node's own, at its own slot, with
rate limiting. -/
theorem slotted_one {τ W : ℕ} (hl : cfg.limit = some (τ, W))
    (x : BlockId × Block Validator BlockId Payload) :
    slotted cfg [x] = [(x.1, slotOf x.2)] := by
  simp [slotted, hl]

omit [Fintype Validator] [LinearOrder BlockId] in
theorem filter_slot_one (j : BlockId) (sl sl' : Validator × ℕ) :
    ([(j, sl')].filter fun e => decide (e.2 = sl)).length = if sl' = sl then 1 else 0 := by
  by_cases h : sl' = sl <;> simp [h]

omit [Fintype Validator] in
/-- The base a bootstrap keeps charges each slot at most once: its blocks
have distinct authors. -/
theorem keptBase_slot_le {τ W : ℕ} (hl : cfg.limit = some (τ, W))
    (l : List (BlockId × Block Validator BlockId Payload)) (sl : Validator × ℕ) :
    ((slotted cfg (keptBase cfg l)).filter fun e => decide (e.2 = sl)).length ≤ 1 := by
  have hp : (keptBase cfg l).Pairwise fun x y => x.2.creator ≠ y.2.creator := by
    simp only [keptBase, hl]; exact List.pairwise_pwFilter _
  simp only [slotted, hl, Option.isSome_some, if_true, List.filter_map, List.length_map]
  generalize keptBase cfg l = k at hp
  change (k.filter fun e => decide (slotOf e.2 = sl)).length ≤ 1
  have hq := hp.filter (fun e => decide (slotOf e.2 = sl))
  generalize hk : k.filter _ = k' at hq ⊢
  have hall : ∀ x ∈ k', slotOf x.2 = sl := by
    intro x hx; rw [← hk] at hx; simpa using (List.mem_filter.mp hx).2
  match k', hq, hall with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: _, hq, hall =>
    exfalso
    have hxy := List.rel_of_pairwise_cons hq List.mem_cons_self
    have h₁ := hall x List.mem_cons_self
    have h₂ := hall y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact hxy (by rw [← h₂] at h₁; exact (Prod.mk.inj h₁).1)

omit [Fintype Validator] in
/-- **A state with the same store, pending blocks, top and charges** keeps
the invariant. -/
theorem Lim.of_eq {τ W : ℕ} {s s' : State Validator BlockId Payload} (h : Lim τ W s)
    (hst : s'.store = s.store) (hpd : s'.pending = s.pending) (htop : s'.top = s.top)
    (how : s'.owner = s.owner) : Lim τ W s' := by
  have hc : ∀ sl, s'.charge sl = s.charge sl := fun sl => by simp only [State.charge, how]
  exact ⟨by rw [hst, how]; exact h.store, by rw [hpd, how]; exact h.pend,
    by rw [how, hst, htop]; exact h.slots, fun sl => by rw [hc]; exact h.charge sl,
    fun sl hsl => by rw [hc]; exact h.fresh sl (by rw [← htop]; exact hsl),
    by rw [hst, htop]; exact h.base⟩

/-! ## Accepting and flushing -/

omit [Fintype Validator] in
theorem accept_in {K : Set (BlockId × Block Validator BlockId Payload)}
    {st : Store Validator BlockId Payload} (hK : ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    ∀ j ∈ (accept cfg st id b).ids,
      (j, (accept cfg st id b).map.getD j (accept cfg st id b).junk) ∈ K := by
  unfold accept
  split
  · exact known_insert hK hb
  · exact hK

omit [Fintype Validator] in
theorem foldl_in {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => accept cfg s e.1 e.2) st
    ∀ j ∈ st'.ids, (j, st'.map.getD j st'.junk) ∈ K
  | [], _, hK, _ => hK
  | e :: l, _, hK, hl =>
    foldl_in l (accept_in hK (hl e List.mem_cons_self)) fun x hx => hl x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
/-- **A flush holds only what it was given**: the store's blocks and the
pending ones. -/
theorem flush_in {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
      {pend : List (BlockId × Block Validator BlockId Payload)},
    (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) → (∀ e ∈ pend, e ∈ K) →
    let r := flush cfg fuel st pend
    (∀ j ∈ r.1.ids, (j, r.1.map.getD j r.1.junk) ∈ K) ∧ ∀ e ∈ r.2, e ∈ K
  | 0, _, _, hK, hp => ⟨hK, hp⟩
  | fuel + 1, st, pend, hK, hp => by
    unfold flush
    dsimp only
    split
    · exact ⟨hK, hp⟩
    · rw [List.partition_eq_filter_filter]
      exact flush_in fuel (foldl_in _ hK fun e he => hp e (List.mem_filter.mp he).1)
        fun e he => hp e (List.mem_filter.mp he).1

omit [Fintype Validator] in
/-- **A flush keeps the invariant.** -/
theorem Lim.flushAll {τ W : ℕ} {s : State Validator BlockId Payload} (h : Lim τ W s) (fuel : ℕ) :
    let fl := flush cfg fuel s.store s.pending
    Lim τ W { s with store := fl.1, pending := fl.2 } := by
  intro fl
  have hf := flush_in (cfg := cfg) (K := {x | Charged s.owner x}) fuel (st := s.store)
    (pend := s.pending) h.store h.pend
  have hb : fl.1.base = s.store.base := flush_base _ _ _
  exact ⟨hf.1, hf.2, by rw [show fl.1.base = s.store.base from hb]; exact h.slots, h.charge,
    h.fresh, by change fl.1.base ≤ _; rw [hb]; exact h.base⟩

/-! ## Building, deciding and collecting -/

omit [Fintype Validator] in
/-- **A successful build step**, with its charge. -/
theorem tryBuild_slot {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    ∃ r id, ∃ b : Block Validator BlockId Payload, ∃ hnew hab hrefs hpred,
      s.top = some r ∧ b.round = r + 1 ∧
      s'.store = s.store.insert id b hnew hab hrefs hpred ∧ s'.top = some (r + 1) ∧
      s'.pending = s.pending ∧ s'.owner = slotted cfg [(id, b)] ++ s.owner := by
  unfold tryBuild at h
  split at h
  · rename_i r hr
    dsimp only at h
    split at h
    · split at h
      · rename_i hc
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨r, _, _, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hr, rfl, rfl, rfl, rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- **Adding a block of the node's own** at round `r + 1`, above its top
`r`, charged to its slot, keeps the invariant. -/
theorem Lim.build {τ W : ℕ} (hl : cfg.limit = some (τ, W)) {s s' : State Validator BlockId Payload}
    (h : Lim τ W s) {r : ℕ} {x : BlockId × Block Validator BlockId Payload}
    (htop : ∀ t ∈ s.top, t = r) (hr : s.store.base ≤ x.2.round) (hxr : x.2.round = r + 1 ∨
      (s.top = none ∧ x.2.round = 0))
    (hst : ∀ j ∈ s'.store.ids, (j, s'.store.map.getD j s'.store.junk) ∈
      {y | Charged s.owner y} ∪ {x})
    (hpd : s'.pending = s.pending) (htop' : s'.top = some x.2.round)
    (hbase : s'.store.base = s.store.base) (how : s'.owner = slotted cfg [x] ++ s.owner) :
    Lim τ W s' := by
  rw [slotted_one hl] at how
  have hfr : ∀ t ∈ s.top, t < x.2.round := by
    intro t ht
    rcases hxr with hxr | ⟨hn, -⟩
    · rw [htop t ht, hxr]; omega
    · rw [hn] at ht; cases ht
  have hcs : ∀ sl, s'.charge sl = (if slotOf x.2 = sl then 1 else 0) + s.charge sl := by
    intro sl
    simp only [State.charge, how]
    rw [List.singleton_append, ← List.singleton_append, charge_append, filter_slot_one]
  have hold : s.top.getD 0 ≤ x.2.round := by
    cases ht : s.top with
    | none => simp
    | some t => have := hfr t ht; simp; omega
  have hmono : ∀ y : BlockId × Block Validator BlockId Payload,
      Charged s.owner y → Charged s'.owner y :=
    fun y => charged_mono fun e he => by rw [how]; exact List.mem_cons_of_mem _ he
  have hself : Charged s'.owner x := ⟨(x.1, slotOf x.2), by rw [how]; exact List.mem_cons_self,
    rfl, le_refl _⟩
  refine ⟨fun j hj => ?_, fun e he => ?_, fun e he => ?_, fun sl => ?_, fun sl hsl => ?_, ?_⟩
  · rcases hst j hj with hj | hj
    · exact hmono _ hj
    · rw [Set.mem_singleton_iff] at hj; rw [hj]; exact hself
  · rw [hpd] at he; exact hmono _ (h.pend e he)
  · rw [hbase, htop']
    rw [how] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hr, by simp [slotOf]⟩
    · have := h.slots e he
      simp only [Option.getD_some]
      omega
  · rw [hcs]
    split
    · rename_i he
      have := h.fresh sl (fun t ht => by rw [← he]; exact hfr t ht)
      omega
    · have := h.charge sl; omega
  · rw [hcs]
    split
    · rename_i he
      rw [htop'] at hsl
      have := hsl _ rfl
      rw [← he] at this
      exact absurd this (lt_irrefl _)
    · refine Nat.zero_add _ ▸ h.fresh sl fun t ht => ?_
      have := hsl _ (by rw [htop']; rfl)
      have := hfr t ht
      omega
  · rw [hbase, htop']; simp only [Option.getD_some]; exact h.base.trans hold

omit [Fintype Validator] in
/-- **A build step keeps the invariant.** -/
theorem Lim.tryBuild {τ W : ℕ} (hl : cfg.limit = some (τ, W))
    {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Lim τ W s)
    (hb : tryBuild cfg s = some (s', out)) : Lim τ W s' := by
  obtain ⟨r, id, b, hnew, hab, hrefs, hpred, hr, hbr, hst, htop, hpd, how⟩ := tryBuild_slot hb
  refine h.build hl (x := (id, b)) (r := r)
    (fun t ht => by rw [hr] at ht; exact (Option.some.inj ht).symm)
    hab (Or.inl hbr) ?_ hpd (by rw [htop, hbr]) (by rw [hst]; rfl) how
  rw [hst]
  exact known_insert (K := {y | Charged s.owner y} ∪ {(id, b)})
    (fun j hj => Set.mem_union_left _ (show _ ∈ {y | Charged s.owner y} from h.store j hj))
    (Set.mem_union_right _ (Set.mem_singleton _))

omit [Fintype Validator] in
theorem Lim.progress {τ W : ℕ} (hl : cfg.limit = some (τ, W)) :
    ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Lim τ W s →
      Lim τ W (progress cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact Lim.progress hl fuel (h.tryBuild hl hb)
    · exact h

omit [Fintype Validator] in
theorem Lim.decideStep {τ W : ℕ} {s : State Validator BlockId Payload} (h : Lim τ W s) :
    Lim τ W (decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · refine h.of_eq ?_ ?_ ?_ ?_ <;> (unfold proposeAt record; dsimp only; split <;> rfl)
  · exact h

omit [Fintype Validator] in
theorem Lim.collect {τ W : ℕ} {s : State Validator BlockId Payload} (h : Lim τ W s) :
    Lim τ W (collect cfg s).1 := by
  unfold Node.collect
  split
  · rename_i t ht
    dsimp only
    split
    · rename_i hG
      set G := min (cfg.per * (min s.lo s.certHeight / cfg.m)) t - cfg.lag with hGd
      have hO : ∀ y : BlockId × Block Validator BlockId Payload, Charged s.owner y →
          cfg.lag ≤ cfg.lag → G ≤ y.2.round →
          Charged (s.owner.filter fun e => G ≤ e.2.2) y := by
        intro y ⟨e, he, h₁, h₂⟩ _ hy
        exact ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true (by omega)⟩, h₁, h₂⟩
      refine ⟨fun j hj => ?_, fun e he => ?_, fun e he => ?_, fun sl => ?_, fun sl hsl => ?_, ?_⟩
      · have hj' := Finset.mem_filter.mp hj
        have hjr : G ≤ (s.store.map.getD j s.store.junk).round := by
          have := hj'.2; simp only [Store.blk, lookup, atBase_round] at this; exact this
        have hraw := treeMap_getD_filter_of (t := s.store.map)
          (f := fun _ b => decide (G ≤ b.round)) (k := j) (fb := s.store.junk)
          (decide_eq_true hjr)
        change Charged _ (j, (s.store.map.filter _).getD j s.store.junk)
        rw [hraw]
        exact hO _ (h.store j hj'.1) le_rfl hjr
      · obtain ⟨he, hr⟩ := List.mem_filter.mp he
        exact hO _ (h.pend e he) le_rfl (of_decide_eq_true hr)
      · obtain ⟨he, hr⟩ := List.mem_filter.mp he
        exact ⟨of_decide_eq_true hr, (h.slots e he).2⟩
      · exact (charge_filter_le _ _ sl).trans (h.charge sl)
      · exact (charge_filter_le _ _ sl).trans (h.fresh sl hsl)
      · change G ≤ _
        rw [ht]; simp only [Option.getD_some]; omega
    · exact h
  · exact h

omit [Fintype Validator] in
/-- **Advancing keeps the invariant.** -/
theorem Lim.advance {τ W : ℕ} (hl : cfg.limit = some (τ, W)) {s : State Validator BlockId Payload}
    (h : Lim τ W s) : Lim τ W (advance cfg s).1 :=
  ((h.progress hl _).decideStep.collect).flushAll _

omit [Fintype Validator] in
theorem Lim.tryResume {τ W : ℕ} {s s' : State Validator BlockId Payload} (h : Lim τ W s)
    (hr : tryResume cfg s = some s') : Lim τ W s' := by
  obtain ⟨t, R, ht, htR, -, -, hst, hpd, htop, -⟩ := tryResume_some hr
  have how : s'.owner = s.owner := by
    unfold Node.tryResume at hr
    split at hr
    · dsimp only at hr
      split at hr
      · split at hr
        · rw [Option.some.injEq] at hr; subst hr; rfl
        · cases hr
      · cases hr
    · cases hr
  have hc : ∀ sl, s'.charge sl = s.charge sl := fun sl => by simp only [State.charge, how]
  refine ⟨by rw [hst, how]; exact h.store, by rw [hpd, how]; exact h.pend, fun e he => ?_,
    fun sl => by rw [hc]; exact h.charge sl, fun sl hsl => ?_, ?_⟩
  · rw [how] at he
    have := h.slots e he
    rw [hst, htop]; rw [ht] at this; simp only [Option.getD_some] at this ⊢; omega
  · rw [hc]
    refine h.fresh sl fun t' ht' => ?_
    rw [ht] at ht'; cases ht'
    have := hsl R (by rw [htop]; rfl)
    omega
  · rw [hst, htop]; have := h.base; rw [ht] at this; simp only [Option.getD_some] at this ⊢; omega

omit [Fintype Validator] in
theorem Lim.settle {τ W : ℕ} (hl : cfg.limit = some (τ, W)) {s : State Validator BlockId Payload}
    (h : Lim τ W s) : Lim τ W (Node.settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hr, he⟩ <;> rw [he]
  · exact h.advance hl
  · exact (h.tryResume hr).advance hl

/-! ## Bootstrapping -/

omit [Fintype Validator] in
/-- The kept base lies at its round. -/
theorem round_of_mem_keptBase {s : State Validator BlockId Payload} {G : ℕ}
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ keptBase cfg (baseAt cfg s G)) :
    x.2.round = G := by
  have := (List.mem_filter.mp (mem_keptBase hx)).2
  simp only [decide_eq_true_eq] at this
  exact this.1

omit [Fintype Validator] in
/-- **A bootstrap keeps the invariant**: what survives the new horizon `G`
keeps its charge, and the kept base is charged at its own slots at `G`,
above the old top. -/
theorem Lim.tryBoot {τ W : ℕ} (hl : cfg.limit = some (τ, W))
    {s s' : State Validator BlockId Payload}
    {ads : List (ℕ × Option BlockId)} (h : Lim τ W s) (hb : tryBoot cfg s = some (s', ads)) :
    Lim τ W s' := by
  obtain ⟨t, G, c, hbase, ht, htG, -, -, hst, hpd, htop', -, -, -, -, -, -, -, -, -, -, -, -,
    how⟩ := tryBoot_some hb
  have hslot : ∀ e ∈ slotted cfg (keptBase cfg (baseAt cfg s G)), e.2.2 = G := by
    intro e he
    simp only [slotted, hl, Option.isSome_some, if_true, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact round_of_mem_keptBase hx
  have hzero : ∀ sl : Validator × ℕ, sl.2 ≠ G →
      ((slotted cfg (keptBase cfg (baseAt cfg s G))).filter fun e => decide (e.2 = sl)).length
        = 0 := by
    intro sl hsl
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    have := hslot e he
    simp only [decide_eq_true_eq]
    rintro rfl
    exact hsl this
  have hO : ∀ y : BlockId × Block Validator BlockId Payload, Charged s.owner y → G ≤ y.2.round →
      Charged s'.owner y := by
    intro y ⟨e, he, h₁, h₂⟩ hy
    exact ⟨e, by rw [how]; exact List.mem_append_right _ (List.mem_filter.mpr ⟨he, by simp; omega⟩),
      h₁, h₂⟩
  have hK₀ : ∀ j ∈ (s.store.prune G hbase.le).ids,
      (j, (s.store.prune G hbase.le).map.getD j (s.store.prune G hbase.le).junk) ∈
        {y | Charged s'.owner y} := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hraw := treeMap_getD_filter_of (t := s.store.map)
      (f := fun _ b => decide (G ≤ b.round)) (k := j) (fb := s.store.junk)
      (by simpa [Store.blk, lookup] using hj'.2)
    change Charged _ (j, (s.store.map.filter _).getD j s.store.junk)
    rw [hraw]
    exact hO _ (h.store j hj'.1) (by simpa [Store.blk, lookup] using hj'.2)
  have hK₁ := foldl_in (cfg := cfg) (keptBase cfg (baseAt cfg s G)) hK₀ fun x hx =>
    ⟨(x.1, slotOf x.2), by
      rw [how]
      refine List.mem_append_left _ ?_
      simp only [slotted, hl, Option.isSome_some, if_true, List.mem_map]
      exact ⟨x, hx, rfl⟩, rfl, le_refl _⟩
  have hlim : cfg.limit.isSome = true := by rw [hl]; rfl
  have hpend : ∀ e ∈ (if cfg.limit.isSome then [] else (s.offers.flatMap (·.2.2)).filter (fun e =>
        decide (G < e.2.round ∧ e.1 = cfg.idOf e.2))) ++ s.pending.filter (fun e => G ≤ e.2.round),
      e ∈ {y | Charged s'.owner y} := by
    intro e he
    rw [if_pos hlim, List.nil_append] at he
    obtain ⟨he, hr⟩ := List.mem_filter.mp he
    exact hO _ (h.pend e he) (of_decide_eq_true hr)
  have hbase' : s'.store.base = G := by
    rw [hst, flush_base, foldl_base]; rfl
  have hc : ∀ sl, s'.charge sl ≤ (if sl.2 = G then 1 else 0) + s.charge sl := by
    intro sl
    simp only [State.charge, how]
    rw [charge_append]
    have := charge_filter_le s.owner (fun e => decide (G ≤ e.2.2)) sl
    split
    · have := keptBase_slot_le hl (baseAt cfg s G) sl; omega
    · rw [hzero sl (by assumption)]; omega
  refine ⟨by rw [hst]; exact (flush_in _ hK₁ hpend).1, by rw [hpd]; exact (flush_in _ hK₁ hpend).2,
    fun e he => ?_, fun sl => ?_,
    fun sl hsl => ?_, ?_⟩
  · rw [hbase', htop']
    simp only [Option.getD_some]
    rw [how] at he
    rcases List.mem_append.mp he with he | he
    · rw [hslot e he]; omega
    · obtain ⟨he, hr⟩ := List.mem_filter.mp he
      have := (h.slots e he).2
      rw [ht] at this
      simp only [Option.getD_some, decide_eq_true_eq] at this hr
      omega
  · refine (hc sl).trans ?_
    split
    · rename_i hG
      have := h.fresh sl fun t' ht' => by rw [ht] at ht'; cases ht'; omega
      omega
    · have := h.charge sl; omega
  · refine (hc sl).trans ?_
    have hG : G < sl.2 := hsl G (by rw [htop']; rfl)
    rw [if_neg (by omega), Nat.zero_add]
    exact h.fresh sl fun t' ht' => by rw [ht] at ht'; cases ht'; omega
  · rw [hbase', htop']; rfl

omit [Fintype Validator] in
theorem Lim.bootFrom {τ W : ℕ} (hl : cfg.limit = some (τ, W)) {s : State Validator BlockId Payload}
    (h : Lim τ W s) : Lim τ W (bootFrom cfg s).1 := by
  rcases bootFrom_cases (cfg := cfg) s with he | ⟨s₂, ads, hbt, he⟩ <;> rw [he]
  · exact h
  · exact (h.tryBoot hl hbt).advance hl

/-! ## A step -/

omit [Fintype Validator] [DecidableEq Validator] in
/-- The slot a block was charged to is a slot of a charge. -/
theorem mem_of_ownerOf {s : State Validator BlockId Payload} {j : BlockId} {sl : Validator × ℕ}
    (h : s.ownerOf j = some sl) : ∃ e ∈ s.owner, e.2 = sl := by
  unfold State.ownerOf at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

omit [Fintype Validator] in
/-- **A kept delivery is charged** to a slot no lower than its round,
within the window, with room for it. -/
theorem chargeTo_spec {τ W : ℕ} {s : State Validator BlockId Payload} (h : Lim τ W s)
    {id : BlockId} {b : Block Validator BlockId Payload} (hab : s.store.base ≤ b.round)
    {sl : Validator × ℕ} (hc : chargeTo τ W s id b = some sl) :
    b.round ≤ sl.2 ∧ s.store.base ≤ sl.2 ∧ sl.2 ≤ s.top.getD 0 + W ∧ s.charge sl < τ := by
  unfold chargeTo at hc
  split at hc
  · rename_i hw
    rw [Option.some.injEq] at hc
    subst hc
    exact ⟨le_refl _, hab, hw.1, by rw [hw.2.1]; exact hw.2.2⟩
  · rename_i hw
    obtain ⟨hsl, hf⟩ := Option.filter_eq_some_iff.mp hc
    have hf' := of_decide_eq_true hf
    obtain ⟨e, he, hfe⟩ := Option.bind_eq_some_iff.mp hsl
    obtain ⟨e', he', rfl⟩ := mem_of_ownerOf hfe
    exact ⟨hf'.2, (h.slots e' he').1, (h.slots e' he').2, hf'.1⟩

omit [Fintype Validator] in
/-- **Taking a kept delivery in** keeps the invariant: it is charged to
its slot, which has room for it. -/
theorem Lim.afterFlush {τ W : ℕ} (hl : cfg.limit = some (τ, W))
    {s : State Validator BlockId Payload}
    (h : Lim τ W s) {id : BlockId} {b : Block Validator BlockId Payload} (hc : Admits cfg s id b) :
    Lim τ W (afterFlush (cfg := cfg) s id b) := by
  obtain ⟨-, -, hab, -, -, hk⟩ := hc
  simp only [kept, hl] at hk
  obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨hbr, hlo, hhi, hroom⟩ := chargeTo_spec h hab hsl
  have hch : charged cfg s id b = [(id, sl)] := by simp [charged, hl, hsl]
  let s₀ : State Validator BlockId Payload :=
    { s with pending := (id, b) :: s.pending, owner := (id, sl) :: s.owner }
  have hcs : ∀ sl', s₀.charge sl' = (if sl = sl' then 1 else 0) + s.charge sl' := by
    intro sl'
    simp only [s₀, State.charge]
    rw [← List.singleton_append, charge_append, filter_slot_one]
  have hmono : ∀ y : BlockId × Block Validator BlockId Payload,
      Charged s.owner y → Charged s₀.owner y :=
    fun y => charged_mono fun e he => List.mem_cons_of_mem _ he
  have h₀ : Lim τ W s₀ := by
    refine ⟨fun j hj => hmono _ (h.store j hj), fun e he => ?_, fun e he => ?_, fun sl' => ?_,
      fun sl' hsl' => ?_, h.base⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨(id, sl), List.mem_cons_self, rfl, hbr⟩
      · exact hmono _ (h.pend e he)
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hlo, hhi⟩
      · exact h.slots e he
    · rw [hcs]; split
      · rename_i he; subst he; omega
      · have := h.charge sl'; omega
    · rw [hcs]; split
      · rename_i he; subst he; omega
      · have := h.fresh sl' hsl'; omega
  have := h₀.flushAll (cfg := cfg) (s.pending.length + 1)
  unfold Node.afterFlush
  rw [hch]
  exact this

/-- **Every step keeps the invariant.** -/
theorem Lim.step {τ W : ℕ} (hl : cfg.limit = some (τ, W)) {s : State Validator BlockId Payload}
    (h : Lim τ W s) (i : Input Validator BlockId Payload) : Lim τ W (Node.step cfg s i).1 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · rename_i h₁
      split
      · rename_i h₂
        refine Lim.settle hl (Lim.build hl h (r := 0) (x := (cfg.idOf cfg.genesis, cfg.genesis))
          (fun t ht => by rw [h₁.1] at ht; cases ht) h₂.2.1 (Or.inr ⟨h₁.1, rfl⟩) ?_ rfl rfl rfl rfl)
        exact known_insert (K := {y | Charged s.owner y} ∪ {(cfg.idOf cfg.genesis, cfg.genesis)})
          (hnew := h₂.1) (hab := h₂.2.1) (hrefs := fun _ => Finset.empty_subset _)
          (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
          (fun j hj => Set.mem_union_left _ (show _ ∈ {y | Charged s.owner y} from h.store j hj))
          (Set.mem_union_right _ (Set.mem_singleton _))
      · exact h
    · exact h
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]
      exact Lim.settle hl ((h.afterFlush hl hc).of_eq rfl rfl rfl rfl)
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hc
      simp only [Node.step, if_neg h']; exact h
  | timer r => exact Lim.settle hl (h.of_eq rfl rfl rfl rfl)
  | fetchRequest peer ids => exact h
  | restart =>
    refine Lim.settle hl ⟨h.store, fun e he => absurd he List.not_mem_nil, h.slots, h.charge,
      h.fresh, h.base⟩
  | baseRequest => exact h
  | baseOffer p G bs =>
    rw [step_offer]
    split
    · exact Lim.bootFrom hl (h.of_eq rfl rfl rfl rfl)
    · exact h
  | certOffer p c =>
    rw [step_certOffer]
    split
    · exact Lim.bootFrom hl (h.of_eq rfl rfl rfl rfl)
    · exact h
  | proposal p k ds =>
    rw [step_proposal]
    split
    · exact h.of_eq rfl rfl rfl rfl
    · exact h

/-- **A run keeps the invariant.** -/
theorem Lim.run {τ W : ℕ} (hl : cfg.limit = some (τ, W)) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload},
      Lim τ W s → Lim τ W (Node.run cfg s is).1
  | [], _, h => h
  | i :: is, _, h => Lim.run hl is (h.step hl i)

omit [Fintype Validator] in
/-- The state before start holds nothing. -/
theorem Lim.init {τ W : ℕ} : Lim τ W (State.init cfg) where
  store := fun _ hj => absurd hj (Finset.notMem_empty _)
  pend := fun _ he => absurd he List.not_mem_nil
  slots := fun _ he => absurd he List.not_mem_nil
  charge := fun _ => by simp [State.charge, State.init]
  fresh := fun _ _ => by simp [State.charge, State.init]
  base := le_refl _

end Node

end LeanDag
