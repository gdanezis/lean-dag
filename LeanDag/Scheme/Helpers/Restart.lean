import LeanDag.Scheme.Helpers.TryDecide
/-!
# Restarting the commit loop

The scan lists each slot with the loop's decision for it, and a slot's
decision reads only the slots above it, so `tryDecide lo N` is the
decided run of `decisionAt N` from `lo` (`tryDecide_eq`). Two facts about
such runs give the restart:

* dropping `j` decided entries from a run is the run from `lo + j`
  (`run_drop`), so restarting inside the output repeats its tail
  (`tryDecide_restart`);
* a run is a prefix of another when every decision of the first is a
  decision of the second (`run_prefix`). A decision on a view is a
  derivation bounded by the scan's last slot, which holds on every larger
  view and which the loop then decides at every larger scan
  (`decisionAt_mono`), so the output on a view is a prefix of the output
  on a larger view (`tryDecide_resume`).
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} [S : Slots Validator]
variable {U : BlockRecord Validator BlockId Payload P honest} {V : U.View}

omit [Fintype Validator] in
/-- **The scan lists each slot with the loop's decision for it.** -/
theorem scan_eq_map (N : ℕ) : ∀ m, m ≤ N + 1 →
    scan p σ U V N m = (List.range' (N + 1 - m) m).map (fun k => (k, decisionAt p σ U V N k))
  | 0, _ => by simp [scan]
  | m + 1, hm => by
    have h1 : decideSlot p σ U V (N - m) (scan p σ U V N m) = decisionAt p σ U V N (N - m) := by
      unfold decisionAt; rw [show N - (N - m) = m by omega]
    show (N - m, decideSlot p σ U V (N - m) (scan p σ U V N m)) :: scan p σ U V N m = _
    rw [h1, scan_eq_map N m (by omega), show N + 1 - (m + 1) = N - m by omega, List.range'_succ,
      List.map_cons, show N + 1 - m = N - m + 1 by omega]

omit [Fintype Validator] in
/-- `tryDecide lo N` is the decided run of `decisionAt N` from `lo`. -/
theorem tryDecide_eq {lo N : ℕ} (hlo : lo ≤ N + 1) :
    tryDecide p σ U V lo N = ((((List.range' lo (N + 1 - lo)).map
      (fun k => (k, decisionAt p σ U V N k))).takeWhile (fun e => e.2.isSome)).map
        (fun e => (e.1, e.2.join))) := by
  unfold tryDecide
  rw [scan_eq_map N _ (by omega), show N + 1 - (N + 1 - lo) = lo by omega]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] S in
/-- **Dropping decided entries from a run** is the run from further up. -/
theorem run_drop {β : Type} (d : ℕ → Option β) : ∀ (j lo n : ℕ),
    j ≤ (((List.range' lo n).map (fun k => (k, d k))).takeWhile (fun e => e.2.isSome)).length →
    (((List.range' lo n).map (fun k => (k, d k))).takeWhile (fun e => e.2.isSome)).drop j =
      ((List.range' (lo + j) (n - j)).map (fun k => (k, d k))).takeWhile (fun e => e.2.isSome)
  | 0, lo, n, _ => by simp
  | j + 1, lo, 0, h => by simp at h
  | j + 1, lo, n + 1, h => by
    simp only [List.range'_succ, List.map_cons, List.takeWhile_cons] at h ⊢
    split
    · rename_i hs
      rw [if_pos hs, List.length_cons] at h
      rw [List.drop_succ_cons, run_drop d j (lo + 1) n (by omega),
        show lo + 1 + j = lo + (j + 1) by omega, show n + 1 - (j + 1) = n - j by omega]
    · rename_i hs
      rw [if_neg hs] at h
      simp at h

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] S in
/-- **A run is a prefix of another** when every decision of the first is a
decision of the second. -/
theorem run_prefix {β : Type} (d₁ d₂ : ℕ → Option β) : ∀ (n₁ lo n₂ : ℕ), n₁ ≤ n₂ →
    (∀ k, lo ≤ k → k < lo + n₁ → ∀ v, d₁ k = some v → d₂ k = some v) →
    ((List.range' lo n₁).map (fun k => (k, d₁ k))).takeWhile (fun e => e.2.isSome) <+:
      ((List.range' lo n₂).map (fun k => (k, d₂ k))).takeWhile (fun e => e.2.isSome)
  | 0, _, _, _, _ => by simp
  | n₁ + 1, lo, 0, h, _ => by omega
  | n₁ + 1, lo, n₂ + 1, h, hd => by
    simp only [List.range'_succ, List.map_cons, List.takeWhile_cons]
    cases h₁ : d₁ lo with
    | none => simp
    | some v =>
      have h₂ := hd lo le_rfl (by omega) v h₁
      simp only [h₂, Option.isSome_some, if_true]
      exact (List.prefix_cons_inj _).mpr (run_prefix d₁ d₂ n₁ (lo + 1) n₂ (by omega)
        fun k h1 h2 => hd k (by omega) (by omega))

omit [Fintype Validator] in
/-- **Restarting inside the output repeats its tail.** -/
theorem tryDecide_restart {lo lo' N : ℕ} (hlo : lo ≤ lo')
    (hlo' : lo' ≤ lo + (tryDecide p σ U V lo N).length) :
    tryDecide p σ U V lo' N = (tryDecide p σ U V lo N).drop (lo' - lo) := by
  by_cases hN : lo ≤ N + 1
  · have hlen := (tryDecide_eq (p := p) (σ := σ) (U := U) (V := V) hN ▸ hlo')
    simp only [List.length_map] at hlen
    have hle := (List.takeWhile_sublist (fun e : ℕ × Option (Option BlockId) => e.2.isSome)
      (l := (List.range' lo (N + 1 - lo)).map (fun k => (k, decisionAt p σ U V N k)))).length_le
    simp only [List.length_map, List.length_range'] at hle
    rw [tryDecide_eq hN, tryDecide_eq (by omega), ← List.map_drop,
      run_drop _ (lo' - lo) lo _ (by omega), show lo + (lo' - lo) = lo' by omega,
      show N + 1 - lo - (lo' - lo) = N + 1 - lo' by omega]
  · have h0 : tryDecide p σ U V lo N = [] := by
      unfold tryDecide; rw [show N + 1 - lo = 0 by omega]; simp [scan]
    rw [h0] at hlo' ⊢
    simp only [List.length_nil] at hlo'
    rw [show lo' = lo by omega]
    unfold tryDecide; rw [show N + 1 - lo = 0 by omega]; simp [scan]

/-- **A decision on a view is the loop's decision on every larger view**,
at every larger scan, when the rule has its laws. -/
theorem decisionAt_mono (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {V₁ V₂ : U.View} (hsub : V₁.ids ⊆ V₂.ids)
    {N₁ N₂ k : ℕ} (hN : N₁ ≤ N₂) (hk : k ≤ N₁) {v : Option BlockId}
    (h : decisionAt p σ U V₁ N₁ k = some v) : decisionAt p σ U V₂ N₂ k = some v := by
  have hmem : (k, decisionAt p σ U V₁ N₁ k) ∈ scan p σ U V₁ N₁ (N₁ + 1 - k) := by
    rw [scan_eq_map N₁ _ (by omega), show N₁ + 1 - (N₁ + 1 - k) = k by omega]
    exact List.mem_map.mpr ⟨k, List.mem_range'_1.mpr ⟨le_rfl, by omega⟩, rfl⟩
  have hd := ((scan_sound (σ := σ) (U := U) (V := V₁) hl hc N₁ (N₁ + 1 - k) (by omega)).2 _
    hmem v h).1
  exact decisionAt_complete hl hcm hc hlaws hI (by omega) (hd.view_mono hlaws hI hsub)

/-- **Resuming on a larger view**: the output on a view, followed by the
output on a larger view from the slot after it, is the output on the
larger view. -/
theorem tryDecide_resume (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {V₁ V₂ : U.View} (hsub : V₁.ids ⊆ V₂.ids)
    {lo N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    tryDecide p σ U V₁ lo N₁ ++
        tryDecide p σ U V₂ (lo + (tryDecide p σ U V₁ lo N₁).length) N₂ =
      tryDecide p σ U V₂ lo N₂ := by
  by_cases hlo : lo ≤ N₁ + 1
  · have hpre : tryDecide p σ U V₁ lo N₁ <+: tryDecide p σ U V₂ lo N₂ := by
      rw [tryDecide_eq hlo, tryDecide_eq (by omega)]
      exact (run_prefix _ _ (N₁ + 1 - lo) lo (N₂ + 1 - lo) (by omega)
        fun k _ h2 v hv => decisionAt_mono hl hcm hc hlaws hI hsub hN (by omega) hv).map _
    obtain ⟨t, ht⟩ := hpre
    have hlen : lo + (tryDecide p σ U V₁ lo N₁).length ≤
        lo + (tryDecide p σ U V₂ lo N₂).length := by
      rw [← ht, List.length_append]; omega
    rw [tryDecide_restart (V := V₂) (by omega) hlen, Nat.add_sub_cancel_left, ← ht,
      List.drop_left]
  · have h0 : tryDecide p σ U V₁ lo N₁ = [] := by
      unfold tryDecide; rw [show N₁ + 1 - lo = 0 by omega]; simp [scan]
    rw [h0, List.nil_append, List.length_nil, Nat.add_zero]

/-- **Successive calls output what one call outputs**: the decisions output
by `t + 1` calls on growing views are the output of one call on the last. -/
theorem consumed_eq (hl : 1 ≤ p.linkSize) (hcm : 1 ≤ p.commitThreshold)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) {lo : ℕ} {W : ℕ → U.View}
    {N : ℕ → ℕ} (hW : ∀ t, (W t).ids ⊆ (W (t + 1)).ids) (hN : ∀ t, N t ≤ N (t + 1)) :
    ∀ t, consumed p σ U lo W N (t + 1) = tryDecide p σ U (W t) lo (N t)
  | 0 => by simp [consumed]
  | t + 1 => by
    rw [consumed, consumed_eq hl hcm hc hlaws hI hW hN t]
    exact tryDecide_resume hl hcm hc hlaws hI (hW t) (hN t)

end Scheme

end LeanDag
