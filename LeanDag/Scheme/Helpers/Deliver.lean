import LeanDag.Scheme.Model.Deliver
/-!
# The delivered sequence — lemmas

`keepFirst` splits over an append, preserves prefixes, keeps distinct keys
and a representative of every key; `Before` survives extension and, in a
duplicate-free sequence, restriction to a prefix holding its later
element. On these, `deliverOf` preserves prefixes, delivers each pair of
round and author at most once, delivers only blocks of the record, and
delivers every honest block a committed leader reaches.
-/

namespace LeanDag

section KeepFirst

variable {α β : Type*} [DecidableEq β] (key : α → β)

/-- **`keepFirst` splits over an append**, the second part continuing from
what the first part saw. -/
theorem keepFirst_append (l₁ l₂ : List α) (seen : List β) :
    ∃ seen', keepFirst key seen (l₁ ++ l₂) = keepFirst key seen l₁ ++ keepFirst key seen' l₂ := by
  induction l₁ generalizing seen with
  | nil => exact ⟨seen, rfl⟩
  | cons a l ih =>
    by_cases h : key a ∈ seen
    · obtain ⟨s', hs'⟩ := ih seen
      exact ⟨s', by simp [keepFirst, h, hs']⟩
    · obtain ⟨s', hs'⟩ := ih (key a :: seen)
      exact ⟨s', by simp [keepFirst, h, hs']⟩

/-- `keepFirst` preserves prefixes. -/
theorem keepFirst_prefix {l₁ l₂ : List α} (h : l₁ <+: l₂) (seen : List β) :
    keepFirst key seen l₁ <+: keepFirst key seen l₂ := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨s', hs'⟩ := keepFirst_append key l₁ t seen
  exact ⟨_, hs'.symm⟩

/-- `keepFirst` keeps a sublist. -/
theorem keepFirst_sublist (l : List α) (seen : List β) : List.Sublist (keepFirst key seen l) l := by
  induction l generalizing seen with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    by_cases h : key a ∈ seen
    · simpa [keepFirst, h] using (ih seen).cons a
    · simpa [keepFirst, h] using (ih (key a :: seen)).cons_cons a

/-- **`keepFirst` keeps distinct keys**, none of them seen. -/
theorem keepFirst_nodup (l : List α) (seen : List β) :
    ((keepFirst key seen l).map key).Nodup ∧ ∀ a ∈ keepFirst key seen l, key a ∉ seen := by
  induction l generalizing seen with
  | nil => simp [keepFirst]
  | cons a l ih =>
    by_cases h : key a ∈ seen
    · simpa [keepFirst, h] using ih seen
    · obtain ⟨hn, hs⟩ := ih (key a :: seen)
      have e : keepFirst key seen (a :: l) = a :: keepFirst key (key a :: seen) l := by
        simp [keepFirst, h]
      rw [e, List.map_cons, List.nodup_cons]
      refine ⟨⟨fun hm => ?_, hn⟩, fun c hc => ?_⟩
      · obtain ⟨c, hc, hca⟩ := List.mem_map.mp hm
        exact hs c hc (hca ▸ List.mem_cons_self ..)
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact h
        · exact fun hm => hs c hc (List.mem_cons_of_mem _ hm)

/-- **`keepFirst` keeps a representative of every unseen key.** -/
theorem exists_keepFirst {l : List α} {a : α} (ha : a ∈ l) {seen : List β}
    (hs : key a ∉ seen) : ∃ c ∈ keepFirst key seen l, key c = key a := by
  induction l generalizing seen with
  | nil => simp at ha
  | cons b l ih =>
    by_cases h : key b ∈ seen
    · have hal : a ∈ l := by
        rcases List.mem_cons.mp ha with rfl | hal
        · exact absurd h hs
        · exact hal
      simpa [keepFirst, h] using ih hal hs
    · by_cases hab : key b = key a
      · exact ⟨b, by simp [keepFirst, h], hab⟩
      · have hal : a ∈ l := by
          rcases List.mem_cons.mp ha with rfl | hal
          · exact absurd rfl hab
          · exact hal
        have hs' : key a ∉ key b :: seen := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun e => hab e.symm, hs⟩
        obtain ⟨c, hc, hca⟩ := ih hal hs'
        exact ⟨c, by simp [keepFirst, h, hc], hca⟩

/-- **Distinct keys leave at most one element of a key class.** -/
theorem length_filter_le_one {l : List α} (hn : (l.map key).Nodup) (q : α → Bool)
    (hq : ∀ a c, q a → q c → key a = key c) : (l.filter q).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases ha : q a
    · have hnil : l.filter q = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr fun c hc => ?_
        obtain ⟨hcl, hqc⟩ := List.mem_filter.mp hc
        exact hn.1 (List.mem_map.mpr ⟨c, hcl, hq c a hqc ha⟩)
      simp [List.filter_cons, ha, hnil]
    · simpa [List.filter_cons, ha] using ih hn.2

end KeepFirst

section Before

variable {α : Type*} {s s' : List α} {x y : α}

/-- Both elements of `Before` occur in the sequence. -/
theorem Before.mem (h : Before s x y) : x ∈ s ∧ y ∈ s := by
  obtain ⟨i, j, -, hi, hj⟩ := h
  exact ⟨List.mem_of_getElem? hi, List.mem_of_getElem? hj⟩

/-- **`Before` survives extension.** -/
theorem Before.of_prefix (h : Before s x y) (hp : s <+: s') : Before s' x y := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  obtain ⟨t, rfl⟩ := hp
  have hjl : j < s.length := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨i, j, hij, ?_, ?_⟩
  · rw [List.getElem?_append_left (by omega)]; exact hi
  · rw [List.getElem?_append_left hjl]; exact hj

/-- **In a duplicate-free sequence, `Before` is asymmetric.** -/
theorem Before.asymm (hn : s.Nodup) (h : Before s x y) : ¬ Before s y x := by
  rintro ⟨i', j', hij', hi', hj'⟩
  obtain ⟨i, j, hij, hi, hj⟩ := h
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hil', e₁⟩ := List.getElem?_eq_some_iff.mp hi'
  obtain ⟨hjl', e₂⟩ := List.getElem?_eq_some_iff.mp hj'
  have h₁ : i' = j := (hn.getElem_inj_iff).mp e₁
  have h₂ : j' = i := (hn.getElem_inj_iff).mp e₂
  omega

/-- **`Before` restricts to a prefix holding the later element**, in a
duplicate-free sequence. -/
theorem Before.of_prefix_mem (h : Before s x y) (hp : s' <+: s) (hn : s.Nodup) (hy : y ∈ s') :
    Before s' x y := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  have hks : k < s.length := lt_of_lt_of_le hk hp.length_le
  have hsk : s'[k] = s[k] := hp.getElem hk
  obtain ⟨hjl, ej⟩ := List.getElem?_eq_some_iff.mp hj
  have hkj : k = j := (hn.getElem_inj_iff).mp (by rw [← hsk, ej])
  subst hkj
  refine ⟨i, k, hij, ?_, by simp [hk]⟩
  rw [List.prefix_iff_eq_take.mp hp, List.getElem?_take_of_lt (by omega)]
  exact hi

/-- **Total order, in Sui and Duan's form**, for prefix-comparable
duplicate-free sequences: whoever delivers `y` has delivered `x` first. -/
theorem Before.of_comparable (hc : s <+: s' ∨ s' <+: s) (hn : s.Nodup) (h : Before s x y)
    (hy : y ∈ s') : Before s' x y := by
  rcases hc with hp | hp
  · exact h.of_prefix hp
  · exact h.of_prefix_mem hp hn hy

/-- **Total order, in Sailfish's form**, for prefix-comparable
duplicate-free sequences: nobody delivers `y` before `x`. -/
theorem Before.not_swap (hc : s <+: s' ∨ s' <+: s) (hn : s.Nodup) (hn' : s'.Nodup)
    (h : Before s x y) : ¬ Before s' y x := by
  rcases hc with hp | hp
  · exact (h.of_prefix hp).asymm hn'
  · exact fun h' => h.asymm hn (h'.of_prefix hp)

end Before

namespace Scheme

variable {Validator : Type} [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

omit [DecidableEq Validator] in
/-- A flush holds exactly the blocks of `U` the leader reaches. -/
theorem mem_flush {L b : BlockId} : b ∈ flush U L ↔ b ∈ U.ids ∧ Reaches U L b := by
  simp [flush, List.mem_mergeSort]

/-- **Delivery preserves prefixes** of the decisions. -/
theorem deliverOf_prefix {D₁ D₂ : List (ℕ × Option BlockId)} (h : D₁ <+: D₂) :
    deliverOf U D₁ <+: deliverOf U D₂ := by
  obtain ⟨t, rfl⟩ := h
  unfold deliverOf
  rw [List.filterMap_append, List.flatMap_append]
  exact keepFirst_prefix _ (List.prefix_append _ _) _

/-- **At most one block of each round and author is delivered.** -/
theorem deliverOf_nodup_roundAuthor (D : List (ℕ × Option BlockId)) :
    ((deliverOf U D).map (roundAuthor U)).Nodup :=
  (keepFirst_nodup _ _ _).1

/-- No block is delivered twice. -/
theorem deliverOf_nodup (D : List (ℕ × Option BlockId)) : (deliverOf U D).Nodup :=
  (deliverOf_nodup_roundAuthor D).of_map _

/-- **Every delivered block is a block of the record**, reached by a
committed leader. -/
theorem mem_deliverOf {D : List (ℕ × Option BlockId)} {b : BlockId} (hb : b ∈ deliverOf U D) :
    b ∈ U.ids ∧ ∃ e ∈ D, ∃ L, e.2 = some L ∧ Reaches U L b := by
  have hb' := (keepFirst_sublist _ _ _).subset hb
  simp only [List.mem_flatMap, List.mem_filterMap] at hb'
  obtain ⟨L, ⟨e, he, hL⟩, hbL⟩ := hb'
  obtain ⟨hU, hr⟩ := mem_flush.mp hbL
  exact ⟨hU, e, he, L, hL, hr⟩

/-- **Every honest block a committed leader reaches is delivered.** -/
theorem mem_deliverOf_of {D : List (ℕ × Option BlockId)} {e : ℕ × Option BlockId} (he : e ∈ D)
    {L b : BlockId} (hL : e.2 = some L) (hb : b ∈ U.ids) (hr : Reaches U L b)
    (hh : (U.block b).creator ∈ honest) : b ∈ deliverOf U D := by
  have hm : b ∈ (D.filterMap Prod.snd).flatMap (flush U) :=
    List.mem_flatMap.mpr ⟨L, List.mem_filterMap.mpr ⟨e, he, hL⟩, mem_flush.mpr ⟨hb, hr⟩⟩
  obtain ⟨c, hc, hkey⟩ := exists_keepFirst (roundAuthor U) hm (List.not_mem_nil)
  have hcU := (mem_deliverOf hc).1
  simp only [roundAuthor, Prod.mk.injEq] at hkey
  have : b = c := U.no_equivocation b hb c hcU hh hkey.2.symm hkey.1.symm
  exact this ▸ hc

end Scheme

end LeanDag
