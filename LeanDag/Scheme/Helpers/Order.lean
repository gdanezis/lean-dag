import LeanDag.Scheme.Helpers.Restart
/-!
# The scheme's order is slot order reversed

The scheme's *TryDecide* visits rounds from `rHigh` down to `rLast`, every
`per`-th one, and in each the leader indices from `m − 1` down to `0`
(`schemeOrder`). Slot `j·m + l` is round `per·j` with leader index `l`
under `Slots.uniform per m` (`schemeOrder_uniform`), and the slots the
scheme visits are those from `⌈rLast/per⌉·m` to `⌈(rHigh+1)/per⌉·m − 1`,
downward (`schemeOrder_slots`). Deciding each in turn from the decisions
already made is the scan (`foldr_range'`), so the scheme's loop in its own
order is `tryDecide` (`schemeTryDecide_eq`).
-/

namespace LeanDag

namespace Scheme

/-- Rounding up `x / per` steps by one exactly at a multiple of `per`, which
it then names. -/
theorem ceilDiv_succ {per : ℕ} (hp : 0 < per) (x : ℕ) :
    (x + 1 + per - 1) / per = (x + per - 1) / per + (if x % per = 0 then 1 else 0) ∧
      (x % per = 0 → x / per = (x + per - 1) / per) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < per ∧ x = per * q + r :=
    ⟨x / per, x % per, Nat.mod_lt _ hp, (Nat.div_add_mod x per).symm⟩
  have hmod : (per * q + r) % per = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hdiv : (per * q + r) / per = q := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [hmod, hdiv]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [show per * q + 0 + 1 + per - 1 = per * q + per by omega,
      show per * q + 0 + per - 1 = per * q + (per - 1) by omega, Nat.mul_add_div hp,
      Nat.mul_add_div hp, Nat.div_self hp, Nat.div_eq_of_lt (by omega : per - 1 < per)]
    simp
  · rw [show per * q + r + 1 + per - 1 = per * q + (r + per) by omega,
      show per * q + r + per - 1 = per * q + (r + per - 1) by omega, Nat.mul_add_div hp,
      Nat.mul_add_div hp, Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega),
      Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    simp [show r ≠ 0 by omega]

/-- Rounding up `x / per` is monotone. -/
theorem ceilDiv_mono {per x y : ℕ} (h : x ≤ y) : (x + per - 1) / per ≤ (y + per - 1) / per :=
  Nat.div_le_div_right (by omega)

/-- The slots of one round, leader indices downward. -/
theorem slots_round (per m r : ℕ) :
    ((List.range m).reverse.map (fun l => (r, l))).map (fun rl => slotOf per m rl.1 rl.2) =
      (List.range' (r / per * m) m).reverse := by
  rw [List.map_map, List.map_reverse, List.range_eq_range']
  congr 1
  simp only [Function.comp_def, slotOf]
  rw [List.map_add_range', Nat.add_zero]

/-- **The slots the scheme visits** over the rounds `a, …, a + n − 1`, in its
order, are the slots from `⌈a/per⌉·m` to `⌈(a+n)/per⌉·m − 1`, downward. -/
theorem schemeOrder_slots {per : ℕ} (hp : 0 < per) (m a : ℕ) : ∀ n,
    (((List.range' a n).reverse.filter (fun r => r % per = 0)).flatMap
      (fun r => (List.range m).reverse.map (fun l => (r, l)))).map
        (fun rl => slotOf per m rl.1 rl.2) =
      (List.range' ((a + per - 1) / per * m)
        (((a + n + per - 1) / per - (a + per - 1) / per) * m)).reverse
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hstep, hname⟩ := ceilDiv_succ hp (a + n)
    have hmono : (a + per - 1) / per * m ≤ (a + n + per - 1) / per * m :=
      Nat.mul_le_mul_right m (ceilDiv_mono (by omega))
    rw [List.range'_concat, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.filter_cons, show a + 1 * n = a + n by omega, show a + (n + 1) = a + n + 1 by omega,
      hstep]
    split
    · rename_i hz
      have hc : (a + per - 1) / per ≤ (a + n + per - 1) / per := ceilDiv_mono (by omega)
      have e1 : ((a + n + per - 1) / per + 1 - (a + per - 1) / per) * m =
          ((a + n + per - 1) / per - (a + per - 1) / per) * m + m := by
        rw [Nat.sub_add_comm hc, Nat.add_mul, Nat.one_mul]
      have e2 : (a + per - 1) / per * m + ((a + n + per - 1) / per - (a + per - 1) / per) * m =
          (a + n + per - 1) / per * m := by
        rw [Nat.sub_mul]; omega
      rw [if_pos (by simpa using hz), List.flatMap_cons, List.map_append, slots_round,
        schemeOrder_slots hp m a n, hname (by simpa using hz), e1, ← List.range'_append,
        List.reverse_append, Nat.one_mul, e2]
    · rename_i hz
      rw [if_neg (by simpa using hz), Nat.add_zero, schemeOrder_slots hp m a n]

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} [S : Slots Validator]
variable {U : BlockRecord Validator BlockId Payload P honest} {V : U.View}

omit [Fintype Validator] in
/-- **Deciding slots `lo, …, lo + n − 1` from the top down** is the scan. -/
theorem foldr_range' : ∀ (n lo : ℕ),
    (List.range' lo n).foldr (fun k Sd => (k, decideSlot p σ U V k Sd) :: Sd) [] =
      scan p σ U V (lo + n - 1) n
  | 0, _ => by simp [scan]
  | n + 1, lo => by
    rw [List.range'_succ, List.foldr_cons, foldr_range' n (lo + 1),
      show lo + 1 + n - 1 = lo + n by omega, show lo + (n + 1) - 1 = lo + n by omega]
    simp only [scan, show lo + n - n = lo by omega]

omit [Fintype Validator] in
/-- **The scheme's loop in its own order is `tryDecide`**: over rounds
`rLast, …, rHigh`, every `per`-th, `m` leaders each, it outputs `tryDecide`
from slot `⌈rLast/per⌉·m` to slot `⌈(rHigh+1)/per⌉·m − 1`. -/
theorem schemeTryDecide_eq {per m rLast rHigh : ℕ} (hp : 0 < per) (hm : 0 < m)
    (h : rLast ≤ rHigh + 1) :
    schemeTryDecide p σ U V per m rLast rHigh =
      tryDecide p σ U V ((rLast + per - 1) / per * m) ((rHigh + per) / per * m - 1) := by
  have hslots := schemeOrder_slots hp m rLast (rHigh + 1 - rLast)
  rw [show rLast + (rHigh + 1 - rLast) + per - 1 = rHigh + per by omega] at hslots
  have hpos : 1 ≤ (rHigh + per) / per := (Nat.one_le_div_iff hp).mpr (by omega)
  have hmono : (rLast + per - 1) / per * m ≤ (rHigh + per) / per * m :=
    Nat.mul_le_mul_right m (Nat.div_le_div_right (by omega))
  have hm1 : m ≤ (rHigh + per) / per * m := Nat.le_mul_of_pos_left m hpos
  unfold schemeTryDecide tryDecide
  rw [show ∀ l : List (ℕ × ℕ), l.foldl (fun Sd rl => (slotOf per m rl.1 rl.2,
      decideSlot p σ U V (slotOf per m rl.1 rl.2) Sd) :: Sd) [] =
        (l.map (fun rl => slotOf per m rl.1 rl.2)).foldl
          (fun Sd k => (k, decideSlot p σ U V k Sd) :: Sd) [] from fun l => by rw [List.foldl_map]]
  unfold schemeOrder
  rw [hslots, List.foldl_reverse, foldr_range', Nat.sub_mul]
  congr 3 <;> omega

/-- **The scheme's restart at a round**, when the rule has its laws. A call
over rounds `rLast, …, rHigh₁` on `V₁` whose last decision is slot `k`,
followed by a call on a larger view `V₂` over rounds from `k`'s round
`per·(k/m)` to `rHigh₂ ≥ rHigh₁`, with the slots up to `k` dropped, is
the call on `V₂` over rounds `rLast, …, rHigh₂`. -/
theorem schemeTryDecide_restartRound (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {V₁ V₂ : U.View} (hsub : V₁.ids ⊆ V₂.ids)
    {per m rLast rHigh₁ rHigh₂ : ℕ} (hp : 0 < per) (hm : 0 < m) (h₁ : rLast ≤ rHigh₁ + 1)
    (hH : rHigh₁ ≤ rHigh₂) {k : ℕ} {v : Option BlockId}
    (hlast : (schemeTryDecide p σ U V₁ per m rLast rHigh₁).getLast? = some (k, v)) :
    schemeTryDecide p σ U V₁ per m rLast rHigh₁ ++
        (schemeTryDecide p σ U V₂ per m (per * (k / m)) rHigh₂).filter (fun e => k < e.1) =
      schemeTryDecide p σ U V₂ per m rLast rHigh₂ := by
  set lo := (rLast + per - 1) / per * m with hlo_def
  set C₁ := (rHigh₁ + per) / per
  have hC₁ : 1 ≤ C₁ := (Nat.one_le_div_iff hp).mpr (by omega)
  have hm1 : m ≤ C₁ * m := Nat.le_mul_of_pos_left m hC₁
  have hloC : lo ≤ C₁ * m := Nat.mul_le_mul_right m (Nat.div_le_div_right (by omega))
  have hN : C₁ * m - 1 ≤ (rHigh₂ + per) / per * m - 1 :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_right m (Nat.div_le_div_right (by omega))) 1
  rw [schemeTryDecide_eq hp hm h₁] at hlast ⊢
  rw [schemeTryDecide_eq hp hm (by omega : rLast ≤ rHigh₂ + 1)]
  have hlo₁ : lo ≤ C₁ * m - 1 + 1 := by omega
  -- The output on `V₁` lists slots `lo, …, k`, and `k ≤ N₁`.
  obtain ⟨hr₁, -⟩ := tryDecide_sound (σ := σ) (U := U) (V := V₁) hl hc hlo₁
  have hlen₁ : (tryDecide p σ U V₁ lo (C₁ * m - 1)).length ≤ C₁ * m - 1 + 1 - lo := by
    rw [tryDecide_eq hlo₁, List.length_map]
    have := (List.takeWhile_sublist (fun e : ℕ × Option (Option BlockId) => e.2.isSome)
      (l := (List.range' lo (C₁ * m - 1 + 1 - lo)).map
        (fun j => (j, decisionAt p σ U V₁ (C₁ * m - 1) j)))).length_le
    simpa using this
  have hk : k = lo + (tryDecide p σ U V₁ lo (C₁ * m - 1)).length - 1 ∧
      1 ≤ (tryDecide p σ U V₁ lo (C₁ * m - 1)).length := by
    have h := congrArg (Option.map Prod.fst) hlast
    rw [← List.getLast?_map, hr₁] at h
    cases hn : (tryDecide p σ U V₁ lo (C₁ * m - 1)).length with
    | zero => rw [hn] at h; simp at h
    | succ n =>
      rw [hn, List.range'_concat, List.getLast?_concat] at h
      simp only [Option.map_some, Option.some.injEq] at h
      omega
  -- `k`'s round lies in the second call's range, and its first slot is `(k / m)·m`.
  have hkm : k / m < C₁ := (Nat.div_lt_iff_lt_mul hm).mpr (by omega)
  have hround : per * (k / m) ≤ rHigh₂ + 1 := by
    have h1 : per * C₁ ≤ rHigh₁ + per := Nat.mul_div_le (rHigh₁ + per) per
    have h2 : per * (k / m) ≤ per * (C₁ - 1) := Nat.mul_le_mul_left per (by omega)
    rw [Nat.mul_sub_one] at h2
    omega
  have hceil : (per * (k / m) + per - 1) / per = k / m := by
    rw [show per * (k / m) + per - 1 = per * (k / m) + (per - 1) by omega, Nat.mul_add_div hp,
      Nat.div_eq_of_lt (by omega : per - 1 < per), Nat.add_zero]
  rw [schemeTryDecide_eq hp hm hround, hceil]
  have hlo' : lo ≤ k / m * m := by
    have : (rLast + per - 1) / per ≤ k / m := by
      rw [← Nat.mul_div_cancel ((rLast + per - 1) / per) hm]
      exact Nat.div_le_div_right (by omega)
    exact Nat.mul_le_mul_right m this
  have hk' : k / m * m ≤ k := Nat.div_mul_le_self k m
  -- Resume, then restart inside the resumed output.
  have hres := tryDecide_resume hl hcm hc hlaws hI hsub hN (lo := lo)
  have hlen₂ : k / m * m ≤ lo + (tryDecide p σ U V₂ lo ((rHigh₂ + per) / per * m - 1)).length := by
    rw [← hres, List.length_append]; omega
  rw [tryDecide_restart (by omega) hlen₂, ← hres,
    List.drop_append_of_le_length (by omega), List.filter_append]
  have hT := (tryDecide_sound (σ := σ) (U := U) (V := V₂) hl hc
    (lo := lo + (tryDecide p σ U V₁ lo (C₁ * m - 1)).length)
    (N := (rHigh₂ + per) / per * m - 1) (by omega)).1
  rw [List.filter_eq_nil_iff.mpr ?_, List.filter_eq_self.mpr ?_, List.nil_append]
  · intro e he
    have : e.1 ∈ (tryDecide p σ U V₂ (lo + (tryDecide p σ U V₁ lo (C₁ * m - 1)).length)
        ((rHigh₂ + per) / per * m - 1)).map Prod.fst := List.mem_map_of_mem he
    rw [hT, List.mem_range'_1] at this
    simp only [decide_eq_true_eq]
    omega
  · intro e he
    have : e.1 ∈ (tryDecide p σ U V₁ lo (C₁ * m - 1)).map Prod.fst :=
      List.mem_map_of_mem (List.mem_of_mem_drop he)
    rw [hr₁, List.mem_range'_1] at this
    simp only [decide_eq_true_eq]
    omega

omit [Fintype Validator] [DecidableEq Validator] S in
/-- **The scheme's pairs are their slots' rounds and leader indices** under
`Slots.uniform per m`. -/
theorem schemeOrder_uniform {per m rLast rHigh : ℕ} (hp : 0 < per) (hm : 0 < m)
    {elect : ℕ → Validator}
    {hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂} :
    ∀ rl ∈ schemeOrder per m rLast rHigh,
      (Slots.uniform per m hp hm elect hblock).slotRound (slotOf per m rl.1 rl.2) = rl.1 ∧
        slotOf per m rl.1 rl.2 % m = rl.2 := by
  intro rl hrl
  simp only [schemeOrder, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_reverse,
    List.mem_range, decide_eq_true_eq] at hrl
  obtain ⟨r, ⟨-, hr⟩, l, hl, rfl⟩ := hrl
  refine ⟨?_, ?_⟩
  · simp only [Slots.uniform_slotRound, slotOf]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hl, Nat.zero_add,
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hr)]
  · simp only [slotOf]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

end Scheme

end LeanDag
